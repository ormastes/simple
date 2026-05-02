//! Collection expression lowering: Tuple, Array, VecLiteral, Dict, ArrayRepeat.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_tuple_expr(&mut self, elements: &[HirExpr]) -> MirLowerResult<VReg> {
        let mut elem_regs = Vec::new();
        for elem in elements {
            let reg = self.lower_expr(elem)?;
            // Box native-typed elements so they become RuntimeValues for the tuple
            let needs_int_boxing = matches!(
                elem.ty,
                TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
            );
            let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = elem.ty == TypeId::BOOL || elem.ty == TypeId::I8;
            if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                let boxed = if needs_bool_boxing {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(boxed),
                            target: CallTarget::from_name("rt_value_bool"),
                            args: vec![reg],
                        });
                        boxed
                    })?
                } else if needs_float_boxing {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: reg,
                        });
                        boxed
                    })?
                } else {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: reg,
                        });
                        boxed
                    })?
                };
                elem_regs.push(boxed);
            } else {
                elem_regs.push(reg);
            }
        }
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::TupleLit {
                dest,
                elements: elem_regs,
            });
            dest
        })
    }

    pub(super) fn lower_array_expr(&mut self, elements: &[HirExpr]) -> MirLowerResult<VReg> {
        let mut elem_regs = Vec::new();
        for elem in elements {
            let reg = self.lower_expr(elem)?;
            // Box native-typed elements so they become RuntimeValues for the array
            let needs_int_boxing = matches!(
                elem.ty,
                TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
            );
            let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = elem.ty == TypeId::BOOL || elem.ty == TypeId::I8;
            if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                let boxed = if needs_bool_boxing {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(boxed),
                            target: CallTarget::from_name("rt_value_bool"),
                            args: vec![reg],
                        });
                        boxed
                    })?
                } else if needs_float_boxing {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: reg,
                        });
                        boxed
                    })?
                } else {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: reg,
                        });
                        boxed
                    })?
                };
                elem_regs.push(boxed);
            } else {
                // Strings, objects, etc. are already RuntimeValues
                elem_regs.push(reg);
            }
        }
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ArrayLit {
                dest,
                elements: elem_regs,
            });
            dest
        })
    }

    pub(super) fn lower_vec_literal_expr(&mut self, elements: &[HirExpr]) -> MirLowerResult<VReg> {
        let mut elem_regs = Vec::new();
        for elem in elements {
            elem_regs.push(self.lower_expr(elem)?);
        }
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::VecLit {
                dest,
                elements: elem_regs,
            });
            dest
        })
    }

    pub(super) fn lower_dict_expr(&mut self, pairs: &[(HirExpr, HirExpr)]) -> MirLowerResult<VReg> {
        // Create an empty dict and insert pairs
        // Dict is represented as a runtime value (i64 pointer)
        let pairs_count = pairs.len();

        // Emit call to create empty dict with capacity
        let capacity = std::cmp::max(8, pairs_count * 2) as i64;
        let capacity_reg = self.with_func(|func, current_block| {
            let reg = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstInt {
                dest: reg,
                value: capacity,
            });
            reg
        })?;

        let dict_target = CallTarget::from_name("rt_dict_new");
        let dict_reg = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: Some(dest),
                target: dict_target,
                args: vec![capacity_reg],
            });
            dest
        })?;

        // Insert each pair
        for (key_expr, value_expr) in pairs {
            let key_reg = self.lower_expr(key_expr)?;
            let value_reg = self.lower_expr(value_expr)?;
            let insert_target = CallTarget::from_name("rt_dict_insert");
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: insert_target,
                    args: vec![dict_reg, key_reg, value_reg],
                });
            })?;
        }

        Ok(dict_reg)
    }

    pub(super) fn lower_array_repeat_expr(&mut self, value: &HirExpr, count: &HirExpr) -> MirLowerResult<VReg> {
        // Array repeat: [value; count] - creates array with count copies of value
        // Lower to runtime call: rt_array_repeat(value, count)
        let value_reg = self.lower_expr(value)?;
        let count_reg = self.lower_expr(count)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: Some(dest),
                target: CallTarget::from_name("rt_array_repeat"),
                args: vec![value_reg, count_reg],
            });
            dest
        })
    }
}
