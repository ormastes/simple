// Test utility functions for LLVM backend

// Helper to set up a test function with binary operations
fn setup_test_function<F>(
    &self,
    name: &str,
    a_val: i64,
    b_val: i64,
    build_op: F,
) -> Result<(), CompileError>
where
    F: FnOnce(&Builder, inkwell::values::IntValue, inkwell::values::IntValue) -> Result<inkwell::values::IntValue, CompileError>,
{
    let (module, builder) = self.get_module_and_builder()?;

    // Create function signature: i64 fn()
    let i64_type = self.context.i64_type();
    let fn_type = i64_type.fn_type(&[], false);
    let function = module.add_function(name, fn_type, None);

    // Create entry block
    let entry = self.context.append_basic_block(function, "entry");
    builder.position_at_end(entry);

    // Create constants
    let a = i64_type.const_int(a_val as u64, true);
    let b = i64_type.const_int(b_val as u64, true);

    // Build operation
    let result = build_op(builder, a, b)?;

    // Return result
    builder
        .build_return(Some(&result))
        .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;

    Ok(())
}

/// Helper to get module and builder references for test functions
#[cfg(feature = "llvm")]
fn get_module_and_builder(&self) -> Result<(&Module, &Builder), CompileError> {
    self.create_module("test_module")?;

    let module = self.module.borrow();
    let module = module
        .as_ref()
        .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

    let builder = self.builder.borrow();
    let builder = builder
        .as_ref()
        .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;

    Ok((module, builder))
}

/// Compile a simple arithmetic function for testing
#[cfg(feature = "llvm")]
pub fn compile_simple_function(
    &self,
    name: &str,
    a_val: i64,
    b_val: i64,
) -> Result<(), CompileError> {
    self.setup_test_function(name, a_val, b_val, |builder, a, b| {
        builder
            .build_int_add(a, b, "add")
            .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e)))
    })
}

#[cfg(not(feature = "llvm"))]
pub fn compile_simple_function(
    &self,
    _name: &str,
    _a_val: i64,
    _b_val: i64,
) -> Result<(), CompileError> {
    Err(CompileError::Semantic(
        "LLVM feature not enabled".to_string(),
    ))
}

/// Compile a function with binary operations (for testing)
#[cfg(feature = "llvm")]
pub fn compile_binop_function(
    &self,
    name: &str,
    op: BinOp,
    a_val: i64,
    b_val: i64,
) -> Result<(), CompileError> {
    self.setup_test_function(name, a_val, b_val, |builder, a, b| {
        match op {
            BinOp::Add => builder
                .build_int_add(a, b, "add")
                .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e))),
            BinOp::Sub => builder
                .build_int_sub(a, b, "sub")
                .map_err(|e| CompileError::Semantic(format!("Failed to build sub: {}", e))),
            BinOp::Mul => builder
                .build_int_mul(a, b, "mul")
                .map_err(|e| CompileError::Semantic(format!("Failed to build mul: {}", e))),
            BinOp::Div => builder
                .build_int_signed_div(a, b, "div")
                .map_err(|e| CompileError::Semantic(format!("Failed to build div: {}", e))),
        }
    })
}

#[cfg(not(feature = "llvm"))]
pub fn compile_binop_function(
    &self,
    _name: &str,
    _op: BinOp,
    _a_val: i64,
    _b_val: i64,
) -> Result<(), CompileError> {
    Err(CompileError::Semantic(
        "LLVM feature not enabled".to_string(),
    ))
}

/// Compile a function with conditional logic (for testing)
#[cfg(feature = "llvm")]
pub fn compile_conditional_function(
    &self,
    name: &str,
    cond_val: bool,
    then_val: i64,
    else_val: i64,
) -> Result<(), CompileError> {
    let (module, builder) = self.get_module_and_builder()?;

    // Create function signature: i64 fn()
    let i64_type = self.context.i64_type();
    let bool_type = self.context.bool_type();
    let fn_type = i64_type.fn_type(&[], false);
    let function = module.add_function(name, fn_type, None);

    // Create blocks
    let entry = self.context.append_basic_block(function, "entry");
    let then_bb = self.context.append_basic_block(function, "then");
    let else_bb = self.context.append_basic_block(function, "else");
    let merge_bb = self.context.append_basic_block(function, "merge");

    // Entry block
    builder.position_at_end(entry);
    let cond = bool_type.const_int(cond_val as u64, false);
    builder
        .build_conditional_branch(cond, then_bb, else_bb)
        .map_err(|e| {
            CompileError::Semantic(format!("Failed to build conditional branch: {}", e))
        })?;

    // Then block
    builder.position_at_end(then_bb);
    let then_value = i64_type.const_int(then_val as u64, true);
    builder
        .build_unconditional_branch(merge_bb)
        .map_err(|e| {
            CompileError::Semantic(format!("Failed to build unconditional branch: {}", e))
        })?;

    // Else block
    builder.position_at_end(else_bb);
    let else_value = i64_type.const_int(else_val as u64, true);
    builder
        .build_unconditional_branch(merge_bb)
        .map_err(|e| {
            CompileError::Semantic(format!("Failed to build unconditional branch: {}", e))
        })?;

    // Merge block with phi
    builder.position_at_end(merge_bb);
    let phi = builder
        .build_phi(i64_type, "result")
        .map_err(|e| CompileError::Semantic(format!("Failed to build phi: {}", e)))?;
    phi.add_incoming(&[(&then_value, then_bb), (&else_value, else_bb)]);

    let result = phi.as_basic_value();
    builder
        .build_return(Some(&result))
        .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;

    Ok(())
}

#[cfg(not(feature = "llvm"))]
pub fn compile_conditional_function(
    &self,
    _name: &str,
    _cond_val: bool,
    _then_val: i64,
    _else_val: i64,
) -> Result<(), CompileError> {
    Err(CompileError::Semantic(
        "LLVM feature not enabled".to_string(),
    ))
}
