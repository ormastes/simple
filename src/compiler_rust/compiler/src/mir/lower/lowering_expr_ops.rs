//! Operator expression lowering: Binary, Unary, Cast.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirExpr, HirExprKind, HirType, TypeId, UnaryOp};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_binary_expr(&mut self, op: BinOp, left: &HirExpr, right: &HirExpr) -> MirLowerResult<VReg> {
        // For compound boolean expressions (And, Or), emit condition probes
        // to track each sub-condition for condition/MC-DC coverage (#674)
        if self.coverage_enabled && matches!(op, BinOp::And | BinOp::Or) {
            // Create a decision ID for this compound expression
            let decision_id = self.next_decision_id();

            // Lower left operand and emit condition probe
            let left_reg = self.lower_expr(left)?;
            self.emit_condition_probe(decision_id, left_reg, 0, 0)?;

            // Lower right operand and emit condition probe
            let right_reg = self.lower_expr(right)?;
            self.emit_condition_probe(decision_id, right_reg, 0, 0)?;

            // Compute the final result
            let dest = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BinOp {
                    dest,
                    op,
                    left: left_reg,
                    right: right_reg,
                });
                dest
            })?;

            // Emit decision probe for the overall result
            self.emit_decision_probe(dest, 0, 0)?;

            Ok(dest)
        } else {
            // `is` against a qualified enum variant (e.g. `a is E.A` or `a is E::A`):
            // The RHS is either Global("E::A") (bare field access, no args) or
            // Call{Global("E::A"), []} (called with no args). In both cases the HIR
            // type is HirType::Enum. Plain pointer equality (icmp) always fails because
            // LHS and RHS are distinct heap allocations. Emit
            // rt_enum_check_discriminant(lhs, disc) where disc is the same hash used
            // by rt_enum_new / match patterns. We check this BEFORE lowering the RHS
            // to avoid emitting the dead rt_enum_new constructor call.
            if op == BinOp::Is {
                let rhs_global_name: Option<&str> = match &right.kind {
                    HirExprKind::Global(name) => Some(name.as_str()),
                    HirExprKind::Call { func, .. } => {
                        if let HirExprKind::Global(name) = &func.kind {
                            Some(name.as_str())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(gname) = rhs_global_name {
                    let variant_name: Option<&str> =
                        gname.rsplit_once("::").or_else(|| gname.rsplit_once('.')).map(|(_, v)| v);
                    let is_enum_rhs = variant_name.is_some()
                        && self
                            .type_registry
                            .and_then(|tr| tr.get(right.ty))
                            .is_some_and(|ty| matches!(ty, HirType::Enum { .. }));
                    if let (true, Some(variant)) = (is_enum_rhs, variant_name) {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut hasher = DefaultHasher::new();
                        variant.hash(&mut hasher);
                        let disc = (hasher.finish() & 0xFFFFFFFF) as i64;
                        let left_reg = self.lower_expr(left)?;
                        return self.with_func(|func, current_block| {
                            let disc_reg = func.new_vreg();
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ConstInt {
                                dest: disc_reg,
                                value: disc,
                            });
                            block.instructions.push(MirInst::Call {
                                dest: Some(dest),
                                target: crate::mir::CallTarget::from_name("rt_enum_check_discriminant"),
                                args: vec![left_reg, disc_reg],
                            });
                            dest
                        });
                    }
                }
            }

            // Non-coverage path or non-boolean operations
            let left_reg = self.lower_expr(left)?;
            let right_reg = self.lower_expr(right)?;

            // Equality involving ANY needs runtime dispatch because native/source
            // paths can carry mixed boxed/raw RuntimeValue-like representations
            // across extern boundaries (for example channel receive).
            if matches!(op, BinOp::Eq | BinOp::Is | BinOp::NotEq) && (left.ty == TypeId::ANY || right.ty == TypeId::ANY)
            {
                let boxed_left = if left.ty == TypeId::ANY && right.ty != TypeId::ANY {
                    left_reg
                } else {
                    self.box_arg_for_any_param(left_reg, left)?
                };
                let boxed_right = if right.ty == TypeId::ANY && left.ty != TypeId::ANY {
                    right_reg
                } else {
                    self.box_arg_for_any_param(right_reg, right)?
                };
                let target = match op {
                    BinOp::Eq | BinOp::Is => "rt_native_eq",
                    BinOp::NotEq => "rt_native_neq",
                    _ => unreachable!(),
                };
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name(target),
                        args: vec![boxed_left, boxed_right],
                    });
                    dest
                });
            }

            // When both operands are ANY-typed (untyped fn params), dispatch
            // to rt_any_add which does a runtime tag check: string operands
            // go through rt_string_concat, integers use arithmetic addition.
            // This matches the interpreter's BinOp::Add runtime dispatch on Value.
            if op == BinOp::Add && left.ty == TypeId::ANY && right.ty == TypeId::ANY {
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_any_add"),
                        args: vec![left_reg, right_reg],
                    });
                    dest
                });
            }

            // Only use string concat when at least one operand is known STRING.
            // ANY-typed operands (untyped fn params) do not reach here for Add —
            // they are handled above. Sub/Mul always emit BinOp.
            let is_string_add = op == BinOp::Add && (left.ty == TypeId::STRING || right.ty == TypeId::STRING);
            let is_array_add = op == BinOp::Add
                && self
                    .type_registry
                    .and_then(|tr| tr.get(left.ty))
                    .is_some_and(|ty| matches!(ty, HirType::Array { .. }))
                && self
                    .type_registry
                    .and_then(|tr| tr.get(right.ty))
                    .is_some_and(|ty| matches!(ty, HirType::Array { .. }));
            if is_string_add {
                // Convert non-string side to string via rt_to_string if needed
                let left_str = if left.ty != TypeId::STRING && left.ty != TypeId::ANY {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: crate::mir::CallTarget::from_name("rt_to_string"),
                            args: vec![left_reg],
                        });
                        dest
                    })?
                } else {
                    left_reg
                };
                let right_str = if right.ty != TypeId::STRING && right.ty != TypeId::ANY {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: crate::mir::CallTarget::from_name("rt_to_string"),
                            args: vec![right_reg],
                        });
                        dest
                    })?
                } else {
                    right_reg
                };
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_string_concat"),
                        args: vec![left_str, right_str],
                    });
                    dest
                })
            } else if is_array_add {
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_array_concat"),
                        args: vec![left_reg, right_reg],
                    });
                    dest
                })
            } else {
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BinOp {
                        dest,
                        op,
                        left: left_reg,
                        right: right_reg,
                    });
                    dest
                })
            }
        }
    }

    pub(super) fn lower_unary_expr(&mut self, op: UnaryOp, operand: &HirExpr) -> MirLowerResult<VReg> {
        let operand_reg = self.lower_expr(operand)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::UnaryOp {
                dest,
                op,
                operand: operand_reg,
            });
            dest
        })
    }

    pub(super) fn lower_cast_expr(&mut self, inner: &HirExpr, target: TypeId) -> MirLowerResult<VReg> {
        let source_reg = self.lower_expr(inner)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Cast {
                dest,
                source: source_reg,
                from_ty: inner.ty,
                to_ty: target,
            });
            dest
        })
    }
}
