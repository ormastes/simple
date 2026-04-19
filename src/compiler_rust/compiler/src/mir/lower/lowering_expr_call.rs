//! Direct and indirect function call expression lowering.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirExprKind, HirType, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_call_expr(
        &mut self,
        callee: &HirExpr,
        args: &[HirExpr],
    ) -> MirLowerResult<VReg> {
        let mut arg_regs = Vec::new();
        for arg in args {
            arg_regs.push(self.lower_expr(arg)?);
        }

        // Direct call or indirect call?
        if let HirExprKind::Global(name) = &callee.kind {
            match (name.as_str(), arg_regs.as_slice()) {
                ("Some", [value]) => {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::OptionSome {
                            dest,
                            value: *value,
                        });
                        dest
                    });
                }
                ("Ok", [value]) => {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ResultOk {
                            dest,
                            value: *value,
                        });
                        dest
                    });
                }
                ("Err", [value]) => {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ResultErr {
                            dest,
                            value: *value,
                        });
                        dest
                    });
                }
                ("None", []) => {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::OptionNone { dest });
                        dest
                    });
                }
                _ => {}
            }

            // Check if this is an enum variant constructor (e.g., "Color::Blue" or "Color.Blue")
            if let Some((enum_name, variant_name)) = name.split_once("::").or_else(|| name.split_once('.')) {
                match (enum_name, variant_name, arg_regs.as_slice()) {
                    ("Option", "Some", [value]) => {
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::OptionSome {
                                dest,
                                value: *value,
                            });
                            dest
                        });
                    }
                    ("Option", "None", []) => {
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::OptionNone { dest });
                            dest
                        });
                    }
                    ("Result", "Ok", [value]) => {
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ResultOk {
                                dest,
                                value: *value,
                            });
                            dest
                        });
                    }
                    ("Result", "Err", [value]) => {
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ResultErr {
                                dest,
                                value: *value,
                            });
                            dest
                        });
                    }
                    _ => {}
                }

                // Check if this is an enum type via the type registry or callee type
                let is_enum = if let Some(registry) = self.type_registry {
                    if let Some(type_id) = registry.lookup(enum_name) {
                        matches!(registry.get(type_id), Some(crate::hir::HirType::Enum { .. }))
                    } else {
                        // Also check the callee's type - if it resolves to an enum
                        matches!(registry.get(callee.ty), Some(crate::hir::HirType::Enum { .. }))
                    }
                } else {
                    false
                };

                if is_enum && !arg_regs.is_empty() {
                    // For single-arg variants, use the arg directly as payload
                    // For multi-arg variants, wrap args in an array as the payload
                    let payload_reg = if arg_regs.len() == 1 {
                        arg_regs[0]
                    } else {
                        // Create an array with all args as the payload
                        let array_reg = self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: Some(dest),
                                target: CallTarget::from_name("rt_array_new"),
                                args: vec![],
                            });
                            dest
                        })?;
                        // Push each arg into the array
                        for arg in &arg_regs {
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: CallTarget::from_name("rt_array_push"),
                                    args: vec![array_reg, *arg],
                                });
                            })?;
                        }
                        array_reg
                    };
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::EnumWith {
                            dest,
                            enum_name: enum_name.to_string(),
                            variant_name: variant_name.to_string(),
                            payload: payload_reg,
                        });
                        dest
                    });
                }
            }

            // Direct call - DI injection is handled at the HIR level
            // The function signature already includes all parameters (including @inject ones)
            // So we don't inject at call sites during MIR lowering
            // NOTE: DI injection at MIR level was causing signature mismatches
            // because functions were registered with all params but calls tried to inject again

            let call_target = CallTarget::from_name(name);
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: call_target,
                    args: arg_regs,
                });
                dest
            })
        } else {
            // Indirect call through closure/function pointer
            let callee_reg = self.lower_expr(callee)?;
            let callee_ty = callee.ty;

            let (param_types, return_type) = if let Some(reg) = self.type_registry {
                if let Some(HirType::Function { params, ret }) = reg.get(callee_ty) {
                    (params.clone(), *ret)
                } else {
                    (vec![TypeId::ANY; arg_regs.len()], TypeId::ANY)
                }
            } else {
                (vec![TypeId::ANY; arg_regs.len()], TypeId::ANY)
            };

            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::IndirectCall {
                    dest: Some(dest),
                    callee: callee_reg,
                    param_types,
                    return_type,
                    args: arg_regs,
                    effect: crate::mir::effects::Effect::Io,
                });
                dest
            })
        }
    }
}
