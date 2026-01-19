/// LLVM instruction compilation - binary ops, unary ops, terminators, coverage
use super::LlvmBackend;
use crate::error::CompileError;

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
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::BinOp;

        // Both operands must be the same type
        match (left, right) {
            (inkwell::values::BasicValueEnum::IntValue(l), inkwell::values::BasicValueEnum::IntValue(r)) => {
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
                    BinOp::Eq => builder
                        .build_int_compare(IntPredicate::EQ, l, r, "eq")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::NotEq => builder
                        .build_int_compare(IntPredicate::NE, l, r, "ne")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::Lt => builder
                        .build_int_compare(IntPredicate::SLT, l, r, "lt")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::LtEq => builder
                        .build_int_compare(IntPredicate::SLE, l, r, "le")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::Gt => builder
                        .build_int_compare(IntPredicate::SGT, l, r, "gt")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::GtEq => builder
                        .build_int_compare(IntPredicate::SGE, l, r, "ge")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_compare", &e))?,
                    BinOp::Mod => builder
                        .build_int_signed_rem(l, r, "mod")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_int_signed_rem", &e))?,
                    BinOp::And => builder
                        .build_and(l, r, "and")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_and", &e))?,
                    BinOp::Or => builder
                        .build_or(l, r, "or")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_or", &e))?,
                    _ => return Err(crate::error::factory::unsupported_operation("integer binop", &op)),
                };
                Ok(result.into())
            }
            (inkwell::values::BasicValueEnum::FloatValue(l), inkwell::values::BasicValueEnum::FloatValue(r)) => {
                let result = match op {
                    BinOp::Add => builder
                        .build_float_add(l, r, "fadd")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_add", &e))?,
                    BinOp::Sub => builder
                        .build_float_sub(l, r, "fsub")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_sub", &e))?,
                    BinOp::Mul => builder
                        .build_float_mul(l, r, "fmul")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_mul", &e))?,
                    BinOp::Div => builder
                        .build_float_div(l, r, "fdiv")
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_float_div", &e))?,
                    _ => return Err(crate::error::factory::unsupported_operation("float binop", &op)),
                };
                Ok(result.into())
            }
            _ => Err(CompileError::Semantic("Type mismatch in binary operation".to_string())),
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
                    _ => {
                        return Err(crate::error::factory::unsupported_operation("integer unary op", &op))
                    }
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
            _ => Err(CompileError::Semantic(
                "Invalid operand type for unary operation".to_string(),
            )),
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
                    builder
                        .build_return(Some(val))
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_return", &e))?;
                } else {
                    return Err(crate::error::factory::undefined_reference("return value", &vreg));
                }
            }
            Terminator::Return(None) => {
                builder
                    .build_return(None)
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

                if let inkwell::values::BasicValueEnum::IntValue(cond_int) = cond_val {
                    let then_bb = llvm_blocks
                        .get(then_block)
                        .ok_or_else(|| crate::error::factory::undefined_reference("block", &then_block))?;
                    let else_bb = llvm_blocks
                        .get(else_block)
                        .ok_or_else(|| crate::error::factory::undefined_reference("block", &else_block))?;

                    builder
                        .build_conditional_branch(*cond_int, *then_bb, *else_bb)
                        .map_err(|e| crate::error::factory::llvm_build_failed("build_conditional_branch", &e))?;
                } else {
                    return Err(CompileError::Semantic("Branch condition must be boolean".to_string()));
                }
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
}
