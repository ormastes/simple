// Test utility methods for LLVM backend.

#[cfg(feature = "llvm")]
use inkwell::IntPredicate;

#[cfg(feature = "llvm")]
use crate::error::{CompileError, ErrorContext, codes};

#[cfg(feature = "llvm")]
use crate::hir::TypeId;

#[cfg(feature = "llvm")]
use crate::mir::BinOp;

#[cfg(feature = "llvm")]
impl LlvmBackend {
    fn const_value(
        &self,
        ty: &TypeId,
        value: i64,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::TypeId as T;
        let val = match *ty {
            T::I32 | T::U32 => self.context.i32_type().const_int(value as u64, true).into(),
            T::I64 | T::U64 => self.context.i64_type().const_int(value as u64, true).into(),
            T::F32 => self.context.f32_type().const_float(value as f64).into(),
            T::F64 => self.context.f64_type().const_float(value as f64).into(),
            T::BOOL => self
                .context
                .bool_type()
                .const_int(if value == 0 { 0 } else { 1 }, false)
                .into(),
            _ => {
                return Err(crate::error::factory::unsupported_constant_type(&ty))
            }
        };

        Ok(val)
    }

    /// Compile a simple function that returns a constant.
    pub fn compile_simple_function(
        &self,
        name: &str,
        param_types: &[TypeId],
        return_type: &TypeId,
        return_val: i64,
    ) -> Result<(), CompileError> {
        self.create_module("test_module")?;
        let module = self.module.borrow();
        let module = module.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM module is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM module not created during compilation".to_string(),
                ctx,
            )
        })?;
        let builder = self.builder.borrow();
        let builder = builder.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM builder is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM builder not created during compilation".to_string(),
                ctx,
            )
        })?;
        let function = self.create_function_signature(name, param_types, return_type)?;

        let entry = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry);

        let ret_val = self.const_value(return_type, return_val)?;
        builder
            .build_return(Some(&ret_val))
            .map_err(|e| crate::error::factory::llvm_build_failed("return", &e))?;

        Ok(())
    }

    /// Compile a function with a binary operation on two parameters.
    pub fn compile_binop_function(
        &self,
        name: &str,
        lhs_type: &TypeId,
        rhs_type: &TypeId,
        return_type: &TypeId,
        op: BinOp,
    ) -> Result<(), CompileError> {
        self.create_module("test_module")?;
        let module = self.module.borrow();
        let module = module.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM module is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM module not created during compilation".to_string(),
                ctx,
            )
        })?;
        let builder = self.builder.borrow();
        let builder = builder.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM builder is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM builder not created during compilation".to_string(),
                ctx,
            )
        })?;
        let function = self.create_function_signature(name, &[lhs_type.clone(), rhs_type.clone()], return_type)?;

        let entry = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry);

        let lhs = function.get_nth_param(0).ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure function parameters are properly initialized");
            CompileError::semantic_with_context(
                "missing left operand parameter in binary operation test function".to_string(),
                ctx,
            )
        })?;
        let rhs = function.get_nth_param(1).ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure function parameters are properly initialized");
            CompileError::semantic_with_context(
                "missing right operand parameter in binary operation test function".to_string(),
                ctx,
            )
        })?;

        let result: inkwell::values::BasicValueEnum<'static> = match *return_type {
            TypeId::F32 | TypeId::F64 => {
                let lhs = lhs.into_float_value();
                let rhs = rhs.into_float_value();
                match op {
                    BinOp::Add => builder.build_float_add(lhs, rhs, "fadd"),
                    BinOp::Sub => builder.build_float_sub(lhs, rhs, "fsub"),
                    BinOp::Mul => builder.build_float_mul(lhs, rhs, "fmul"),
                    BinOp::Div => builder.build_float_div(lhs, rhs, "fdiv"),
                }
                .map_err(|e| crate::error::factory::llvm_build_failed("float op", &e))?
                .into()
            }
            _ => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                match op {
                    BinOp::Add => builder.build_int_add(lhs, rhs, "add"),
                    BinOp::Sub => builder.build_int_sub(lhs, rhs, "sub"),
                    BinOp::Mul => builder.build_int_mul(lhs, rhs, "mul"),
                    BinOp::Div => builder.build_int_signed_div(lhs, rhs, "div"),
                }
                .map_err(|e| crate::error::factory::llvm_build_failed("int op", &e))?
                .into()
            }
        };

        builder
            .build_return(Some(&result))
            .map_err(|e| crate::error::factory::llvm_build_failed("return", &e))?;

        Ok(())
    }

    /// Compile a function with a simple conditional and phi merge.
    pub fn compile_conditional_function(
        &self,
        name: &str,
        cond_type: &TypeId,
        return_type: &TypeId,
        then_val: i64,
        else_val: i64,
    ) -> Result<(), CompileError> {
        self.create_module("test_module")?;
        let module = self.module.borrow();
        let module = module.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM module is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM module not created during compilation".to_string(),
                ctx,
            )
        })?;
        let builder = self.builder.borrow();
        let builder = builder.as_ref().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure LLVM builder is initialized before compilation");
            CompileError::semantic_with_context(
                "LLVM builder not created during compilation".to_string(),
                ctx,
            )
        })?;
        let function = self.create_function_signature(name, &[cond_type.clone()], return_type)?;

        let entry = self.context.append_basic_block(function, "entry");
        let then_bb = self.context.append_basic_block(function, "then");
        let else_bb = self.context.append_basic_block(function, "else");
        let merge_bb = self.context.append_basic_block(function, "merge");

        builder.position_at_end(entry);
        let cond_param = function.get_nth_param(0).ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure function parameters are properly initialized");
            CompileError::semantic_with_context(
                "missing condition parameter in conditional test function".to_string(),
                ctx,
            )
        })?;
        let cond_int = cond_param.into_int_value();
        let zero = cond_int.get_type().const_zero();
        let cond = builder
            .build_int_compare(IntPredicate::SGT, cond_int, zero, "cond")
            .map_err(|e| crate::error::factory::llvm_build_failed("compare", &e))?;
        builder
            .build_conditional_branch(cond, then_bb, else_bb)
            .map_err(|e| crate::error::factory::llvm_build_failed("branch", &e))?;

        builder.position_at_end(then_bb);
        let then_value = self.const_value(return_type, then_val)?;
        builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| crate::error::factory::llvm_build_failed("branch", &e))?;

        builder.position_at_end(else_bb);
        let else_value = self.const_value(return_type, else_val)?;
        builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| crate::error::factory::llvm_build_failed("branch", &e))?;

        builder.position_at_end(merge_bb);
        let phi_type = self.llvm_type(return_type)?;
        let phi = builder
            .build_phi(phi_type, "result")
            .map_err(|e| crate::error::factory::llvm_build_failed("phi", &e))?;
        phi.add_incoming(&[(&then_value, then_bb), (&else_value, else_bb)]);
        let result = phi.as_basic_value();

        builder
            .build_return(Some(&result))
            .map_err(|e| crate::error::factory::llvm_build_failed("return", &e))?;

        Ok(())
    }
}

#[cfg(not(feature = "llvm"))]
impl LlvmBackend {
    pub fn compile_simple_function(
        &self,
        _name: &str,
        _param_types: &[TypeId],
        _return_type: &TypeId,
        _return_val: i64,
    ) -> Result<(), CompileError> {
        let ctx = ErrorContext::new()
            .with_code(codes::UNSUPPORTED_FEATURE)
            .with_help("compile with the 'llvm' feature enabled to use LLVM backend");
        Err(CompileError::semantic_with_context(
            "LLVM backend feature is not enabled".to_string(),
            ctx,
        ))
    }

    pub fn compile_binop_function(
        &self,
        _name: &str,
        _lhs_type: &TypeId,
        _rhs_type: &TypeId,
        _return_type: &TypeId,
        _op: BinOp,
    ) -> Result<(), CompileError> {
        let ctx = ErrorContext::new()
            .with_code(codes::UNSUPPORTED_FEATURE)
            .with_help("compile with the 'llvm' feature enabled to use LLVM backend");
        Err(CompileError::semantic_with_context(
            "LLVM backend feature is not enabled".to_string(),
            ctx,
        ))
    }

    pub fn compile_conditional_function(
        &self,
        _name: &str,
        _cond_type: &TypeId,
        _return_type: &TypeId,
        _then_val: i64,
        _else_val: i64,
    ) -> Result<(), CompileError> {
        let ctx = ErrorContext::new()
            .with_code(codes::UNSUPPORTED_FEATURE)
            .with_help("compile with the 'llvm' feature enabled to use LLVM backend");
        Err(CompileError::semantic_with_context(
            "LLVM backend feature is not enabled".to_string(),
            ctx,
        ))
    }
}
