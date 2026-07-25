//! Operator expression lowering: Binary, Unary, Cast.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirExpr, HirExprKind, HirType, TypeId, UnaryOp};
use crate::mir::blocks::Terminator;
use crate::mir::effects::LocalKind;
use crate::mir::function::MirLocal;
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
        } else if matches!(op, BinOp::And | BinOp::Or) {
            // Short-circuit evaluation. `AndSuspend`/`OrSuspend` (the `and~`/`or~`
            // await-forms) intentionally fall through to the eager path below —
            // only the plain short-circuit operators are handled here.
            //
            // Previously this fell into the generic eager path (both operands
            // lowered unconditionally, then bitwise-ANDed/ORed in codegen), so
            // `x and call()` ran `call()` even when `x` was false — a silent
            // logic-corruption bug when the RHS has side effects (native-build
            // entry-closure defect C3).
            self.lower_short_circuit_logical(op, left, right)
        } else {
            // `is` against a qualified enum variant (e.g. `a is E.A` or `a is E::A`):
            // The RHS is either Global("E::A") (bare field access, no args) or
            // Call{Global("E::A"), []} (called with no args). In both cases the HIR
            // type is HirType::Enum. Plain pointer equality (icmp) always fails because
            // LHS and RHS are distinct heap allocations. Emit a typed pattern test
            // that checks both the enum runtime ID and the variant discriminant. We
            // check this BEFORE lowering the RHS
            // to avoid emitting the dead rt_enum_new constructor call.
            // `is` and `==` against a bare enum variant both reduce to a
            // discriminant test. `==` MUST use it too: for two same-typed enum
            // operands (neither ANY) the fall-through emits a native `icmp` that
            // compares the two enum HEAP POINTERS — a freshly built RHS variant
            // is a different allocation than the LHS, so `p == Policy.Suggested`
            // is ALWAYS false on the freestanding/dynload lane (E=0). Routing a
            // bare-variant `==` through the same typed pattern test fixes it.
            // Restricted to a bare
            // `Global` variant for `==`/`!=`: a payload-carrying constructor
            // (`Some(x)`) is a pure discriminant test only for `is` — `==` there
            // must also compare the payload, so that form stays on the general
            // path. See doc/08_tracking/bug/native_enum_eq_always_false_freestanding_2026-07-19.md.
            if matches!(op, BinOp::Is | BinOp::Eq) {
                let rhs_global_name: Option<&str> = match &right.kind {
                    HirExprKind::Global(name) => Some(name.as_str()),
                    HirExprKind::Call { func, .. } if op == BinOp::Is => {
                        if let HirExprKind::Global(name) = &func.kind {
                            Some(name.as_str())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(gname) = rhs_global_name {
                    let enum_variant = gname
                        .rsplit_once("::")
                        .or_else(|| gname.rsplit_once('.'));
                    let is_enum_rhs = enum_variant.is_some()
                        && self
                            .type_registry
                            .and_then(|tr| tr.get(right.ty))
                            .is_some_and(|ty| matches!(ty, HirType::Enum { .. }));
                    if let (true, Some((enum_name, variant_name))) = (is_enum_rhs, enum_variant) {
                        let left_reg = self.lower_expr(left)?;
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::PatternTest {
                                dest,
                                subject: left_reg,
                                pattern: crate::mir::MirPattern::Variant {
                                    enum_name: enum_name.to_string(),
                                    variant_name: variant_name.to_string(),
                                    payload: None,
                                },
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
                // Convert non-string side to string. Native scalars must be
                // boxed first (BoxInt/BoxFloat/rt_value_bool) — passing a raw
                // i64/f64 to rt_to_string prints "<value:0xN>" (#66).
                let left_str = if left.ty != TypeId::STRING && left.ty != TypeId::ANY {
                    self.emit_to_string(left_reg, left.ty)?
                } else {
                    left_reg
                };
                let right_str = if right.ty != TypeId::STRING && right.ty != TypeId::ANY {
                    self.emit_to_string(right_reg, right.ty)?
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

    /// Lower `left and right` / `left or right` with true short-circuit control
    /// flow: `right` is only evaluated when its value can affect the result.
    /// Mirrors the interpreter's `BinOp::And`/`BinOp::Or` handling
    /// (interpreter/expr/ops.rs) and the block/temp-local merge pattern used
    /// for `HirStmt::If` (lowering_stmt.rs).
    fn lower_short_circuit_logical(&mut self, op: BinOp, left: &HirExpr, right: &HirExpr) -> MirLowerResult<VReg> {
        let left_reg = self.lower_expr(left)?;

        // Temp local to carry the boolean result across the two branches into
        // the merge block (VRegs don't survive block boundaries without a
        // phi/local, same constraint the If-statement lowering works around).
        // Uses TypeId::I64 (not BOOL) to match the proven HirStmt::If merge
        // local exactly: booleans flow as i64 0/1 everywhere else in this
        // codegen (every comparison widens via `ensure_i64` immediately after
        // the icmp), and a BOOL-typed local risks codegen declaring it at i8
        // width while ConstBool/comparisons feed it i64-shaped values.
        let temp_local_index = self.with_func(|func, _| {
            let index = func.params.len() + func.locals.len();
            func.locals.push(MirLocal {
                name: format!("__logical_{}", index),
                ty: TypeId::I64,
                kind: LocalKind::Local,
                is_ghost: false,
            });
            index
        })?;

        let (eval_rhs_block, short_block, merge_block) = self.with_func(|func, current_block| {
            let eval_rhs_block = func.new_block();
            let short_block = func.new_block();
            let merge_block = func.new_block();
            let block = func.block_mut(current_block).unwrap();
            block.terminator = if op == BinOp::And {
                // left is truthy -> must evaluate right; left is falsy -> short-circuit false
                Terminator::Branch {
                    cond: left_reg,
                    then_block: eval_rhs_block,
                    else_block: short_block,
                }
            } else {
                // Or: left is truthy -> short-circuit true; left is falsy -> must evaluate right
                Terminator::Branch {
                    cond: left_reg,
                    then_block: short_block,
                    else_block: eval_rhs_block,
                }
            };
            (eval_rhs_block, short_block, merge_block)
        })?;

        // short_block: result is fully determined by `left` alone.
        self.set_current_block(short_block)?;
        let short_value = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstInt {
                dest,
                value: if op == BinOp::Or { 1 } else { 0 },
            });
            dest
        })?;
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: short_value,
                ty: TypeId::I64,
            });
        })?;
        self.finalize_block_jump(merge_block)?;

        // eval_rhs_block: result is `right`'s truthiness (right is only ever
        // lowered here, never on the short-circuit path).
        self.set_current_block(eval_rhs_block)?;
        let right_reg = self.lower_expr(right)?;
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: right_reg,
                ty: TypeId::I64,
            });
        })?;
        self.finalize_block_jump(merge_block)?;

        // merge_block: load the merged result.
        self.set_current_block(merge_block)?;
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let value = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            block.instructions.push(MirInst::Load {
                dest: value,
                addr,
                ty: TypeId::I64,
            });
            value
        })
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

        // str(x)/text(x) on a native scalar: MirInst::Cast is a plain value
        // copy in codegen, so a raw int/float would masquerade as a STRING
        // pointer — rt_string_concat then sees len=-1 and returns NIL,
        // dropping the whole concat to empty (#66). Convert for real.
        if target == TypeId::STRING && Self::is_native_scalar(inner.ty) {
            return self.emit_to_string(source_reg, inner.ty);
        }

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

    /// True for types whose runtime representation is a raw machine scalar
    /// (not a tagged RuntimeValue).
    fn is_native_scalar(ty: TypeId) -> bool {
        matches!(
            ty,
            TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
                | TypeId::F32
                | TypeId::F64
                | TypeId::BOOL
        )
    }

    /// Emit a to-string conversion for `reg` of type `ty`, boxing native
    /// scalars into RuntimeValues first (mirrors the rt_value_to_string
    /// builtin lowering in lowering_expr_builtin.rs).
    fn emit_to_string(&mut self, reg: VReg, ty: TypeId) -> MirLowerResult<VReg> {
        // U64 must not go through BoxInt (sign issues); use the raw helper.
        if ty == TypeId::U64 {
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::CallTarget::from_name("rt_raw_u64_to_string"),
                    args: vec![reg],
                });
                dest
            });
        }

        self.with_func(|func, current_block| {
            let boxed = match ty {
                TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 => {
                    let boxed = func.new_vreg();
                    func.block_mut(current_block)
                        .unwrap()
                        .instructions
                        .push(MirInst::BoxInt {
                            dest: boxed,
                            value: reg,
                        });
                    boxed
                }
                TypeId::F32 | TypeId::F64 => {
                    let boxed = func.new_vreg();
                    func.block_mut(current_block)
                        .unwrap()
                        .instructions
                        .push(MirInst::BoxFloat {
                            dest: boxed,
                            value: reg,
                        });
                    boxed
                }
                TypeId::BOOL => {
                    let boxed = func.new_vreg();
                    func.block_mut(current_block).unwrap().instructions.push(MirInst::Call {
                        dest: Some(boxed),
                        target: crate::mir::CallTarget::from_name("rt_value_bool"),
                        args: vec![reg],
                    });
                    boxed
                }
                // Heap values (structs, arrays, ...) are already RuntimeValues.
                _ => reg,
            };
            let dest = func.new_vreg();
            func.block_mut(current_block).unwrap().instructions.push(MirInst::Call {
                dest: Some(dest),
                target: crate::mir::CallTarget::from_name("rt_value_to_string"),
                args: vec![boxed],
            });
            dest
        })
    }
}
