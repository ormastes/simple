/// LLVM instruction compilation - binary ops, unary ops, terminators, coverage
use super::LlvmBackend;
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::IntPredicate;

impl LlvmBackend {
    /// Compile a binary operation
    #[cfg(feature = "llvm")]
    pub(super) fn compile_binop(
        &self,
        op: crate::hir::BinOp,
        left: inkwell::values::BasicValueEnum<'static>,
        right: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::BinOp;

        // Both operands must be the same type
        match (left, right) {
            (inkwell::values::BasicValueEnum::IntValue(l), inkwell::values::BasicValueEnum::IntValue(r)) => {
                // Ensure both operands have the same bit width
                let i64_type = self.context.i64_type();
                let l = if l.get_type().get_bit_width() < 64 {
                    builder.build_int_z_extend(l, i64_type, "zext_l")
                        .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                } else { l };
                let r = if r.get_type().get_bit_width() < 64 {
                    builder.build_int_z_extend(r, i64_type, "zext_r")
                        .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                } else { r };

                let result = match op {
                    BinOp::Add => builder
                        .build_int_add(l, r, "add")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_add", &e))?,
                    BinOp::Sub => builder
                        .build_int_sub(l, r, "sub")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_sub", &e))?,
                    BinOp::Mul => builder
                        .build_int_mul(l, r, "mul")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_mul", &e))?,
                    BinOp::Div => builder
                        .build_int_signed_div(l, r, "div")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_signed_div", &e))?,
                    BinOp::Eq => {
                        // Use rt_native_eq for safe equality (handles mixed raw int / tagged string)
                        let rt_func = module.get_function("rt_native_eq").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                            module.add_function("rt_native_eq", fn_type, None)
                        });
                        let call_site = builder
                            .build_call(rt_func, &[l.into(), r.into()], "eq")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_eq", &e))?;
                        call_site.try_as_basic_value().left()
                            .unwrap_or_else(|| i64_type.const_int(0, false).into())
                            .into_int_value()
                    }
                    BinOp::NotEq => {
                        // Use rt_native_neq for safe inequality
                        let rt_func = module.get_function("rt_native_neq").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                            module.add_function("rt_native_neq", fn_type, None)
                        });
                        let call_site = builder
                            .build_call(rt_func, &[l.into(), r.into()], "neq")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_neq", &e))?;
                        call_site.try_as_basic_value().left()
                            .unwrap_or_else(|| i64_type.const_int(0, false).into())
                            .into_int_value()
                    }
                    BinOp::Lt => {
                        let cmp = builder
                            .build_int_compare(IntPredicate::SLT, l, r, "lt")
                            .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?;
                        builder.build_int_z_extend(cmp, i64_type, "lt_i64")
                            .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                    }
                    BinOp::LtEq => {
                        let cmp = builder
                            .build_int_compare(IntPredicate::SLE, l, r, "le")
                            .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?;
                        builder.build_int_z_extend(cmp, i64_type, "le_i64")
                            .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                    }
                    BinOp::Gt => {
                        let cmp = builder
                            .build_int_compare(IntPredicate::SGT, l, r, "gt")
                            .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?;
                        builder.build_int_z_extend(cmp, i64_type, "gt_i64")
                            .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                    }
                    BinOp::GtEq => {
                        let cmp = builder
                            .build_int_compare(IntPredicate::SGE, l, r, "ge")
                            .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?;
                        builder.build_int_z_extend(cmp, i64_type, "ge_i64")
                            .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?
                    }
                    BinOp::Mod => builder
                        .build_int_signed_rem(l, r, "mod")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_signed_rem", &e))?,
                    BinOp::And => builder
                        .build_and(l, r, "and")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_and", &e))?,
                    BinOp::Or => builder
                        .build_or(l, r, "or")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_or", &e))?,
                    BinOp::BitAnd => builder
                        .build_and(l, r, "bitand")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_and", &e))?,
                    BinOp::BitOr => builder
                        .build_or(l, r, "bitor")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_or", &e))?,
                    BinOp::BitXor => builder
                        .build_xor(l, r, "bitxor")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_xor", &e))?,
                    BinOp::ShiftLeft => builder
                        .build_left_shift(l, r, "shl")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_left_shift", &e))?,
                    BinOp::ShiftRight => builder
                        .build_right_shift(l, r, false, "shr")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_right_shift", &e))?,
                    BinOp::Pow => {
                        // Implement power as a runtime call or loop; for now use runtime
                        // Simple: a^b as repeated multiplication would be slow, so just return a placeholder
                        // In practice this should call rt_pow or similar
                        l // placeholder — will be replaced with rt_pow call
                    }
                    // Operators that require runtime support — return first operand as fallback
                    BinOp::In | BinOp::NotIn | BinOp::MatMul | BinOp::Parallel => l,
                    _ => return Err(crate::error::factory::unsupported_operation("integer binop", &op)),
                };
                Ok(result.into())
            }
            (inkwell::values::BasicValueEnum::FloatValue(l), inkwell::values::BasicValueEnum::FloatValue(r)) => {
                use inkwell::FloatPredicate;
                match op {
                    BinOp::Add => Ok(builder
                        .build_float_add(l, r, "fadd")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_add", &e))?
                        .into()),
                    BinOp::Sub => Ok(builder
                        .build_float_sub(l, r, "fsub")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_sub", &e))?
                        .into()),
                    BinOp::Mul => Ok(builder
                        .build_float_mul(l, r, "fmul")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_mul", &e))?
                        .into()),
                    BinOp::Div => Ok(builder
                        .build_float_div(l, r, "fdiv")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_div", &e))?
                        .into()),
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        let pred = match op {
                            BinOp::Eq => FloatPredicate::OEQ,
                            BinOp::NotEq => FloatPredicate::ONE,
                            BinOp::Lt => FloatPredicate::OLT,
                            BinOp::Gt => FloatPredicate::OGT,
                            BinOp::LtEq => FloatPredicate::OLE,
                            BinOp::GtEq => FloatPredicate::OGE,
                            _ => unreachable!(),
                        };
                        let cmp = builder
                            .build_float_compare(pred, l, r, "fcmp")
                            .map_err(|e| crate::error::factory::llvm_build_failed("fcmp", &e))?;
                        let i64_type = self.context.i64_type();
                        let result = builder
                            .build_int_z_extend(cmp, i64_type, "fcmp_ext")
                            .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?;
                        Ok(result.into())
                    }
                    _ => Err(crate::error::factory::unsupported_operation("float binop", &op)),
                }
            }
            (inkwell::values::BasicValueEnum::PointerValue(l), inkwell::values::BasicValueEnum::PointerValue(r)) => {
                // Pointer comparisons: cast to i64 and compare
                let i64_type = self.context.i64_type();
                let l_int = builder
                    .build_ptr_to_int(l, i64_type, "ptrtoint_l")
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_ptr_to_int", &e))?;
                let r_int = builder
                    .build_ptr_to_int(r, i64_type, "ptrtoint_r")
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_ptr_to_int", &e))?;
                let result = match op {
                    BinOp::Eq => {
                        let rt_func = module.get_function("rt_native_eq").unwrap_or_else(|| {
                            let fn_type = self.context.i64_type().fn_type(&[self.context.i64_type().into(), self.context.i64_type().into()], false);
                            module.add_function("rt_native_eq", fn_type, None)
                        });
                        let call_site = builder.build_call(rt_func, &[l_int.into(), r_int.into()], "eq")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_eq", &e))?;
                        call_site.try_as_basic_value().left()
                            .unwrap_or_else(|| self.context.i64_type().const_int(0, false).into())
                            .into_int_value()
                    }
                    BinOp::NotEq => {
                        let rt_func = module.get_function("rt_native_neq").unwrap_or_else(|| {
                            let fn_type = self.context.i64_type().fn_type(&[self.context.i64_type().into(), self.context.i64_type().into()], false);
                            module.add_function("rt_native_neq", fn_type, None)
                        });
                        let call_site = builder.build_call(rt_func, &[l_int.into(), r_int.into()], "neq")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_neq", &e))?;
                        call_site.try_as_basic_value().left()
                            .unwrap_or_else(|| self.context.i64_type().const_int(0, false).into())
                            .into_int_value()
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                        // Arithmetic on pointers (runtime representation): operate on integer form
                        match op {
                            BinOp::Add => builder
                                .build_int_add(l_int, r_int, "ptr_add")
                                .map_err(|e| crate::error::factory::llvm_build_failed("build_int_add", &e))?,
                            BinOp::Sub => builder
                                .build_int_sub(l_int, r_int, "ptr_sub")
                                .map_err(|e| crate::error::factory::llvm_build_failed("build_int_sub", &e))?,
                            BinOp::Mul => builder
                                .build_int_mul(l_int, r_int, "ptr_mul")
                                .map_err(|e| crate::error::factory::llvm_build_failed("build_int_mul", &e))?,
                            BinOp::Div => builder
                                .build_int_signed_div(l_int, r_int, "ptr_div")
                                .map_err(|e| crate::error::factory::llvm_build_failed("build_int_signed_div", &e))?,
                            _ => unreachable!(),
                        }
                    }
                    _ => return Err(crate::error::factory::unsupported_operation("pointer binop", &op)),
                };
                Ok(result.into())
            }
            _ => {
                // Mixed types: cast both to i64 and operate as integers
                let i64_type = self.context.i64_type();
                let l_int = self.coerce_to_int(left, i64_type, builder, "coerce_l")?;
                let r_int = self.coerce_to_int(right, i64_type, builder, "coerce_r")?;

                // Eq/NotEq use rt_native_eq/neq for safe mixed-representation equality
                if matches!(op, BinOp::Eq) {
                    let rt_func = module.get_function("rt_native_eq").unwrap_or_else(|| {
                        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                        module.add_function("rt_native_eq", fn_type, None)
                    });
                    let call_site = builder.build_call(rt_func, &[l_int.into(), r_int.into()], "eq")
                        .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_eq", &e))?;
                    let eq_val = call_site.try_as_basic_value().left()
                        .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        .into_int_value();
                    return Ok(eq_val.into());
                }
                if matches!(op, BinOp::NotEq) {
                    let rt_func = module.get_function("rt_native_neq").unwrap_or_else(|| {
                        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                        module.add_function("rt_native_neq", fn_type, None)
                    });
                    let call_site = builder.build_call(rt_func, &[l_int.into(), r_int.into()], "neq")
                        .map_err(|e| crate::error::factory::llvm_build_failed("rt_native_neq", &e))?;
                    let neq_val = call_site.try_as_basic_value().left()
                        .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        .into_int_value();
                    return Ok(neq_val.into());
                }

                let result = match op {
                    BinOp::Add => builder.build_int_add(l_int, r_int, "mixed_add"),
                    BinOp::Sub => builder.build_int_sub(l_int, r_int, "mixed_sub"),
                    BinOp::Mul => builder.build_int_mul(l_int, r_int, "mixed_mul"),
                    BinOp::Div => builder.build_int_signed_div(l_int, r_int, "mixed_div"),
                    BinOp::Lt => builder.build_int_compare(IntPredicate::SLT, l_int, r_int, "mixed_lt"),
                    BinOp::LtEq => builder.build_int_compare(IntPredicate::SLE, l_int, r_int, "mixed_le"),
                    BinOp::Gt => builder.build_int_compare(IntPredicate::SGT, l_int, r_int, "mixed_gt"),
                    BinOp::GtEq => builder.build_int_compare(IntPredicate::SGE, l_int, r_int, "mixed_ge"),
                    BinOp::Mod => builder.build_int_signed_rem(l_int, r_int, "mixed_mod"),
                    BinOp::And => builder.build_and(l_int, r_int, "mixed_and"),
                    BinOp::Or => builder.build_or(l_int, r_int, "mixed_or"),
                    BinOp::BitAnd => builder.build_and(l_int, r_int, "mixed_bitand"),
                    BinOp::BitOr => builder.build_or(l_int, r_int, "mixed_bitor"),
                    BinOp::BitXor => builder.build_xor(l_int, r_int, "mixed_bitxor"),
                    BinOp::ShiftLeft => builder.build_left_shift(l_int, r_int, "mixed_shl"),
                    BinOp::ShiftRight => builder.build_right_shift(l_int, r_int, false, "mixed_shr"),
                    _ => Ok(l_int), // Fallback for operators like In, NotIn, Pow, etc.
                }
                .map_err(|e| crate::error::factory::llvm_build_failed("mixed_binop", &e))?;
                Ok(result.into())
            }
        }
    }

    /// Coerce a value to an integer type for mixed-type operations
    #[cfg(feature = "llvm")]
    fn coerce_to_int(
        &self,
        val: inkwell::values::BasicValueEnum<'static>,
        int_type: inkwell::types::IntType<'static>,
        builder: &Builder<'static>,
        name: &str,
    ) -> Result<inkwell::values::IntValue<'static>, CompileError> {
        match val {
            inkwell::values::BasicValueEnum::IntValue(v) => {
                // Already integer, bitcast/extend/truncate to target width
                if v.get_type().get_bit_width() == int_type.get_bit_width() {
                    Ok(v)
                } else if v.get_type().get_bit_width() < int_type.get_bit_width() {
                    builder
                        .build_int_s_extend(v, int_type, name)
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_s_extend", &e))
                } else {
                    builder
                        .build_int_truncate(v, int_type, name)
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_truncate", &e))
                }
            }
            inkwell::values::BasicValueEnum::PointerValue(v) => builder
                .build_ptr_to_int(v, int_type, name)
                .map_err(|e| crate::error::factory::llvm_build_failed("build_ptr_to_int", &e)),
            inkwell::values::BasicValueEnum::FloatValue(v) => builder
                .build_float_to_signed_int(v, int_type, name)
                .map_err(|e| crate::error::factory::llvm_build_failed("build_float_to_signed_int", &e)),
            _ => Err(CompileError::semantic(format!(
                "Cannot coerce {:?} to integer",
                val
            ))),
        }
    }

    /// Compile a unary operation
    #[cfg(feature = "llvm")]
    pub(super) fn compile_unaryop(
        &self,
        op: crate::hir::UnaryOp,
        operand: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::UnaryOp;

        match operand {
            inkwell::values::BasicValueEnum::IntValue(val) => {
                let result = match op {
                    UnaryOp::Neg => builder
                        .build_int_neg(val, "neg")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_neg", &e))?,
                    UnaryOp::Not => builder
                        .build_not(val, "not")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_not", &e))?,
                    UnaryOp::BitNot => builder
                        .build_not(val, "bitnot")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_not", &e))?,
                    _ => return Err(crate::error::factory::unsupported_operation("integer unary op", &op)),
                };
                Ok(result.into())
            }
            inkwell::values::BasicValueEnum::FloatValue(val) => {
                let result = match op {
                    UnaryOp::Neg => builder
                        .build_float_neg(val, "fneg")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_neg", &e))?,
                    _ => return Err(crate::error::factory::unsupported_operation("float unary op", &op)),
                };
                Ok(result.into())
            }
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("unary operations are only supported for integers and floats");
                Err(CompileError::semantic_with_context(
                    "Invalid operand type for unary operation".to_string(),
                    ctx,
                ))
            }
        }
    }

    /// Compile a terminator instruction
    #[cfg(feature = "llvm")]
    pub(super) fn compile_terminator(
        &self,
        term: &crate::mir::Terminator,
        llvm_blocks: &std::collections::HashMap<crate::mir::BlockId, inkwell::basic_block::BasicBlock>,
        vreg_map: &std::collections::HashMap<crate::mir::VReg, inkwell::values::BasicValueEnum<'static>>,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        use crate::mir::Terminator;

        match term {
            Terminator::Return(Some(vreg)) => {
                if let Some(val) = vreg_map.get(vreg) {
                    // Coerce return value to i64 (function return type)
                    let i64_type = self.context.i64_type();
                    let coerced = self.coerce_value_to_type(
                        *val,
                        Some(i64_type.into()),
                        builder,
                    )?;
                    builder
                        .build_return(Some(&coerced))
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_return", &e))?;
                } else {
                    // Missing vreg — return 0 as fallback
                    let zero = self.context.i64_type().const_int(0, false);
                    builder
                        .build_return(Some(&zero))
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_return", &e))?;
                }
            }
            Terminator::Return(None) => {
                // All functions return i64 in the tagged-value ABI; void returns become 0
                let zero = self.context.i64_type().const_int(0, false);
                builder
                    .build_return(Some(&zero))
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_return", &e))?;
            }
            Terminator::Jump(block_id) => {
                let target_bb = llvm_blocks
                    .get(block_id)
                    .ok_or_else(|| crate::error::factory::undefined_reference("block", &block_id))?;
                builder
                    .build_unconditional_branch(*target_bb)
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_unconditional_branch", &e))?;
            }
            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond_val = vreg_map
                    .get(cond)
                    .ok_or_else(|| crate::error::factory::undefined_reference("condition", &cond))?;

                let then_bb = llvm_blocks
                    .get(then_block)
                    .ok_or_else(|| crate::error::factory::undefined_reference("block", &then_block))?;
                let else_bb = llvm_blocks
                    .get(else_block)
                    .ok_or_else(|| crate::error::factory::undefined_reference("block", &else_block))?;

                // Coerce condition to i1: truncate i64/i32 to i1, or icmp ne ptr, null
                let cond_i1 = match cond_val {
                    inkwell::values::BasicValueEnum::IntValue(iv) => {
                        let bit_width = iv.get_type().get_bit_width();
                        if bit_width == 1 {
                            *iv
                        } else {
                            // Truncate to i1 (nonzero = true)
                            let zero = iv.get_type().const_int(0, false);
                            builder
                                .build_int_compare(inkwell::IntPredicate::NE, *iv, zero, "tobool")
                                .map_err(|e| crate::error::factory::llvm_build_failed("int_compare", &e))?
                        }
                    }
                    inkwell::values::BasicValueEnum::PointerValue(pv) => {
                        let null = pv.get_type().const_null();
                        builder
                            .build_int_compare(inkwell::IntPredicate::NE,
                                builder.build_ptr_to_int(*pv, self.context.i64_type(), "ptoi")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?,
                                builder.build_ptr_to_int(null, self.context.i64_type(), "nulltoi")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?,
                                "tobool")
                            .map_err(|e| crate::error::factory::llvm_build_failed("int_compare", &e))?
                    }
                    _ => {
                        // Fallback: create a true constant
                        self.context.bool_type().const_int(1, false)
                    }
                };

                builder
                    .build_conditional_branch(cond_i1, *then_bb, *else_bb)
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_conditional_branch", &e))?;
            }
            Terminator::Unreachable => {
                builder
                    .build_unreachable()
                    .map_err(|e| crate::error::factory::llvm_build_failed("build_unreachable", &e))?;
            }
        }

        Ok(())
    }

    /// Emit a coverage counter increment for a basic block
    #[cfg(feature = "llvm")]
    pub(super) fn emit_coverage_counter(
        &self,
        module: &Module,
        builder: &Builder,
        func_name: &str,
        block_id: u32,
    ) -> Result<(), CompileError> {
        // Get next counter id
        let counter_id = {
            let mut counter = self.coverage_counter.borrow_mut();
            let id = *counter;
            *counter += 1;
            id
        };

        // Create global counter variable name
        let counter_name = format!("__simple_cov_{}_{}", func_name, block_id);

        // Check if counter already exists, if not create it
        let counter_global = if let Some(global) = module.get_global(&counter_name) {
            global
        } else {
            let i64_type = self.context.i64_type();
            let global = module.add_global(i64_type, None, &counter_name);
            global.set_initializer(&i64_type.const_zero());
            global.set_linkage(inkwell::module::Linkage::Internal);
            global
        };

        // Load current value
        let i64_type = self.context.i64_type();
        let current = builder
            .build_load(i64_type, counter_global.as_pointer_value(), "cov_load")
            .map_err(|e| crate::error::factory::llvm_build_failed("load coverage counter", &e))?;

        // Increment
        if let inkwell::values::BasicValueEnum::IntValue(current_int) = current {
            let one = i64_type.const_int(1, false);
            let incremented = builder
                .build_int_add(current_int, one, "cov_inc")
                .map_err(|e| crate::error::factory::llvm_build_failed("increment coverage counter", &e))?;

            // Store back
            builder
                .build_store(counter_global.as_pointer_value(), incremented)
                .map_err(|e| crate::error::factory::llvm_build_failed("store coverage counter", &e))?;
        }

        // Track counter for later retrieval
        let _ = counter_id; // Will be used in coverage mapping later

        Ok(())
    }

    /// Coerce a value to match an expected LLVM type.
    ///
    /// Handles ptr→i64 (ptrtoint), i64→ptr (inttoptr), i1→i64 (zext),
    /// i64→i1 (trunc), and float→int / int→float conversions.
    #[cfg(feature = "llvm")]
    pub(super) fn coerce_value_to_type(
        &self,
        val: inkwell::values::BasicValueEnum<'static>,
        expected: Option<inkwell::types::BasicTypeEnum<'static>>,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let expected = match expected {
            Some(t) => t,
            None => return Ok(val), // No expected type, pass through
        };

        use inkwell::types::BasicTypeEnum;
        use inkwell::values::BasicValueEnum;

        match (val, expected) {
            // ptr → i64
            (BasicValueEnum::PointerValue(pv), BasicTypeEnum::IntType(it)) => {
                let cast = builder
                    .build_ptr_to_int(pv, it, "ptrtoint")
                    .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
                Ok(cast.into())
            }
            // i64 → ptr
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::PointerType(pt)) => {
                let cast = builder
                    .build_int_to_ptr(iv, pt, "inttoptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?;
                Ok(cast.into())
            }
            // i1 → i64 (zero-extend)
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::IntType(it))
                if iv.get_type().get_bit_width() < it.get_bit_width() =>
            {
                let cast = builder
                    .build_int_z_extend(iv, it, "zext")
                    .map_err(|e| crate::error::factory::llvm_build_failed("zext", &e))?;
                Ok(cast.into())
            }
            // i64 → i1 (truncate)
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::IntType(it))
                if iv.get_type().get_bit_width() > it.get_bit_width() =>
            {
                let cast = builder
                    .build_int_truncate(iv, it, "trunc")
                    .map_err(|e| crate::error::factory::llvm_build_failed("trunc", &e))?;
                Ok(cast.into())
            }
            // float → int (bitcast to preserve tagged-value ABI bit patterns)
            (BasicValueEnum::FloatValue(fv), BasicTypeEnum::IntType(it))
                if it.get_bit_width() == 64 =>
            {
                let cast = builder
                    .build_bit_cast(fv, it, "f2i")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bitcast_f2i", &e))?;
                Ok(cast.into())
            }
            // float → int (different widths, fall back to fptosi)
            (BasicValueEnum::FloatValue(fv), BasicTypeEnum::IntType(it)) => {
                let cast = builder
                    .build_float_to_signed_int(fv, it, "fptosi")
                    .map_err(|e| crate::error::factory::llvm_build_failed("float_to_int", &e))?;
                Ok(cast.into())
            }
            // int → float (bitcast to preserve tagged-value ABI bit patterns)
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::FloatType(ft))
                if iv.get_type().get_bit_width() == 64 =>
            {
                let cast = builder
                    .build_bit_cast(iv, ft, "i2f")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bitcast_i2f", &e))?;
                Ok(cast.into())
            }
            // int → float (different widths, fall back to sitofp)
            (BasicValueEnum::IntValue(iv), BasicTypeEnum::FloatType(ft)) => {
                let cast = builder
                    .build_signed_int_to_float(iv, ft, "sitofp")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_float", &e))?;
                Ok(cast.into())
            }
            // Types already match or close enough
            _ => Ok(val),
        }
    }
}
