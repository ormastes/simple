//! Built-in call expression lowering (rt_* and print/println family).

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_builtin_call_expr(
        &mut self,
        name: &str,
        args: &[HirExpr],
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
        // Special handling for rt_enum_payload - returns tagged RuntimeValue
        // that needs unboxing when the payload type is a native type
        if name == "rt_enum_payload" && args.len() == 1 {
            let arg_reg = self.lower_expr(&args[0])?;
            let raw_result = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: CallTarget::from_name("rt_enum_payload"),
                    args: vec![arg_reg],
                });
                dest
            })?;

            // rt_enum_payload returns a tagged RuntimeValue.
            // Mark it as tagged so downstream Store/Load tracking can
            // insert UnboxInt when storing to a concrete int-typed local.
            self.tagged_vregs.insert(raw_result);

            // If the expected type is known to be a native int/float, unbox now.
            let needs_int_unbox = matches!(
                expr_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
                    | TypeId::BOOL
            );
            let needs_float_unbox = matches!(expr_ty, TypeId::F32 | TypeId::F64);

            if needs_int_unbox {
                return self.with_func(|func, current_block| {
                    let unboxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::UnboxInt {
                        dest: unboxed,
                        value: raw_result,
                    });
                    unboxed
                });
            } else if needs_float_unbox {
                return self.with_func(|func, current_block| {
                    let unboxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::UnboxFloat {
                        dest: unboxed,
                        value: raw_result,
                    });
                    unboxed
                });
            } else {
                // Strings, arrays, objects are already valid as RuntimeValue pointers
                return Ok(raw_result);
            }
        }

        // Special handling for join
        if name == "join" && args.len() == 1 {
            let actor_reg = self.lower_expr(&args[0])?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ActorJoin { dest, actor: actor_reg });
                dest
            });
        }

        // Special handling for reply
        if name == "reply" && args.len() == 1 {
            let message_reg = self.lower_expr(&args[0])?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ActorReply { message: message_reg });
                // Reply returns nil (represented as 0)
                block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                dest
            });
        }

        // Special handling for rt_value_to_string - box integers/floats
        if name == "rt_value_to_string" && args.len() == 1 {
            let arg = &args[0];
            let arg_reg = self.lower_expr(arg)?;

            // Check if argument is a native integer or float type that needs boxing
            let needs_boxing = matches!(
                arg.ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            );
            let needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = arg.ty == TypeId::BOOL;

            return self.with_func(|func, current_block| {
                // Box the argument if it's a native type
                let boxed_arg = if needs_bool_boxing {
                    // Bool needs special boxing via rt_value_bool to preserve true/false
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(boxed),
                        target: CallTarget::from_name("rt_value_bool"),
                        args: vec![arg_reg],
                    });
                    boxed
                } else if needs_boxing {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: arg_reg,
                    });
                    boxed
                } else if needs_float_boxing {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxFloat {
                        dest: boxed,
                        value: arg_reg,
                    });
                    boxed
                } else {
                    // Strings, arrays, etc. are already RuntimeValues
                    arg_reg
                };

                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: CallTarget::from_name(name),
                    args: vec![boxed_arg],
                });
                dest
            });
        }

        // Special handling for print/println/eprint/eprintln - box numeric args
        if matches!(
            name,
            "print" | "println" | "eprint" | "eprintln" | "print_raw" | "eprint_raw" | "dprint"
        ) {
            let mut boxed_arg_regs = Vec::new();
            for arg in args {
                let arg_reg = self.lower_expr(arg)?;
                let needs_int_boxing = matches!(
                    arg.ty,
                    TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                );
                let needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64);
                let needs_bool_boxing = arg.ty == TypeId::BOOL || arg.ty == TypeId::I8;
                if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                    let boxed = if needs_bool_boxing {
                        // Use rt_value_bool for bool → RuntimeValue conversion
                        self.with_func(|func, current_block| {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: Some(boxed),
                                target: CallTarget::from_name("rt_value_bool"),
                                args: vec![arg_reg],
                            });
                            boxed
                        })?
                    } else {
                        self.with_func(|func, current_block| {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            if needs_int_boxing {
                                block.instructions.push(MirInst::BoxInt {
                                    dest: boxed,
                                    value: arg_reg,
                                });
                            } else {
                                block.instructions.push(MirInst::BoxFloat {
                                    dest: boxed,
                                    value: arg_reg,
                                });
                            }
                            boxed
                        })?
                    };
                    boxed_arg_regs.push(boxed);
                } else {
                    boxed_arg_regs.push(arg_reg);
                }
            }
            let target = CallTarget::from_name(name);
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target,
                    args: boxed_arg_regs,
                });
                dest
            });
        }

        // Lower all arguments
        let mut arg_regs = Vec::new();
        for arg in args {
            arg_regs.push(self.lower_expr(arg)?);
        }

        // Create a call to the builtin function
        let target = CallTarget::from_name(name);
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: Some(dest),
                target,
                args: arg_regs,
            });
            dest
        })
    }
}
