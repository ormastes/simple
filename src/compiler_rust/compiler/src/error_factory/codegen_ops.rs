//! Factory functions: codegen/LLVM, assignment/mutation, tensor/math, unit conversion,
//! parser errors, result/option, math eval, conversion/parse, dependency/resolution,
//! block/custom syntax, FFI/interpreter errors.

use crate::error::{codes, CompileError, ErrorContext};

// ============================================
// Codegen / LLVM Errors
// ============================================

/// Error when an unsupported language feature is encountered during codegen.
pub fn unsupported_feature(feature: &str) -> CompileError {
    CompileError::Codegen(format!("unsupported feature: {}", feature))
}

/// Error when codegen fails with a specific message.
pub fn codegen_failed(message: &str) -> CompileError {
    CompileError::Codegen(message.to_string())
}

/// Error when an unsupported operation is encountered.
pub fn unsupported_operation(operation: &str) -> CompileError {
    CompileError::Codegen(format!("unsupported operation: {}", operation))
}

/// Error when an undefined reference is encountered during codegen.
pub fn undefined_reference(name: &str) -> CompileError {
    CompileError::Codegen(format!("undefined reference to '{}'", name))
}

/// Error when LLVM module verification fails.
pub fn llvm_module_verify_failed(message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM module verification failed: {}", message))
}

/// Error when LLVM JIT compilation fails.
pub fn llvm_jit_failed(message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM JIT compilation failed: {}", message))
}

/// Error when LLVM fails to write a bitcode file.
pub fn llvm_write_bitcode_failed(path: &impl std::fmt::Debug, message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM failed to write bitcode to {:?}: {}", path, message))
}

/// Error when LLVM fails to write an object file.
pub fn llvm_write_object_failed(path: &impl std::fmt::Debug, message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM failed to write object file to {:?}: {}", path, message))
}

/// Error when LLVM fails to set the target triple.
pub fn llvm_target_triple_failed(triple: &str, message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM target triple '{}' failed: {}", triple, message))
}

/// Error when LLVM fails to create a target machine.
pub fn llvm_target_machine_failed(message: &str) -> CompileError {
    CompileError::Codegen(format!("LLVM target machine creation failed: {}", message))
}

/// Error when an unsupported calling convention is used.
pub fn unsupported_calling_convention(convention: &str) -> CompileError {
    CompileError::Codegen(format!("unsupported calling convention: {}", convention))
}

/// Error when an unsupported linkage type is used.
pub fn unsupported_linkage(linkage: &str) -> CompileError {
    CompileError::Codegen(format!("unsupported linkage type: {}", linkage))
}

/// Error when an invalid encoding is encountered.
pub fn invalid_encoding(context: &str, detail: &str) -> CompileError {
    CompileError::Codegen(format!("invalid encoding in {}: {}", context, detail))
}

// ============================================
// Assignment / Mutation Errors
// ============================================

/// Error when an assignment is made to a const binding.
pub fn cannot_assign_to_const(name: &str) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::IMMUTABLE_ASSIGNMENT)
        .with_help(format!("declare '{}' with 'let mut' to allow mutation", name));
    CompileError::semantic_with_context(
        format!("cannot assign to immutable binding '{}'", name),
        ctx,
    )
}

/// Error when a mutation is attempted on an immutable value.
pub fn cannot_mutate_immutable(name: &str) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::IMMUTABLE_ASSIGNMENT)
        .with_help(format!("use 'mut {}' to allow mutation", name));
    CompileError::semantic_with_context(
        format!("cannot mutate immutable value '{}'", name),
        ctx,
    )
}

// ============================================
// Tensor / Shape Errors
// ============================================

/// Error when tensor shapes don't match for an operation.
pub fn tensor_shape_mismatch(op: &str, left: &str, right: &str) -> CompileError {
    CompileError::Semantic(format!(
        "tensor shape mismatch in '{}': left={}, right={}",
        op, left, right
    ))
}

/// Error when a tensor reshape fails.
pub fn tensor_reshape_failed(from: &str, to: &str) -> CompileError {
    CompileError::Semantic(format!(
        "cannot reshape tensor from {} to {}: element count mismatch",
        from, to
    ))
}

/// Error when a tensor dimension index is out of range.
pub fn tensor_dim_out_of_range(index: usize, rank: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor dimension index {} is out of range for rank-{} tensor",
        index, rank
    ))
}

/// Error when a tensor index is out of bounds.
pub fn tensor_index_out_of_bounds(index: usize, size: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor index {} is out of bounds (size={})",
        index, size
    ))
}

/// Error when tensor index count doesn't match tensor rank.
pub fn tensor_index_count_mismatch(expected: usize, found: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor index count mismatch: expected {}, found {}",
        expected, found
    ))
}

/// Error when tensor data length doesn't match shape.
pub fn tensor_data_length_mismatch(data_len: usize, shape_product: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor data length {} doesn't match shape product {}",
        data_len, shape_product
    ))
}

/// Error when tensor.item() is called but the tensor is not scalar.
pub fn tensor_item_requires_scalar(shape: &str) -> CompileError {
    CompileError::Semantic(format!(
        "tensor.item() requires a scalar tensor, got shape {}",
        shape
    ))
}

// ============================================
// Unit Conversion Errors
// ============================================

/// Error when a type has no associated unit family.
pub fn unit_no_family(type_name: &str) -> CompileError {
    CompileError::Semantic(format!("type '{}' has no associated unit family", type_name))
}

/// Error when a unit family is not found.
pub fn unit_family_not_found(family_name: &str) -> CompileError {
    CompileError::Semantic(format!("unit family '{}' not found", family_name))
}

/// Error when a unit is not in its expected family.
pub fn unit_not_in_family(unit_name: &str, family_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "unit '{}' is not in family '{}'",
        unit_name, family_name
    ))
}

/// Error when a target unit is not found in the registry.
pub fn target_unit_not_found(unit_name: &str) -> CompileError {
    CompileError::Semantic(format!("target unit '{}' not found in registry", unit_name))
}

/// Error when a non-numeric type is used in a unit conversion.
pub fn unit_non_numeric_conversion(type_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "cannot perform unit conversion on non-numeric type '{}'",
        type_name
    ))
}

// ============================================
// Parser Errors
// ============================================

/// Error when an expected token is not found.
pub fn expected_token(expected: &str, found: &str) -> CompileError {
    CompileError::Parse(format!("expected {}, found {}", expected, found))
}

/// Error when an unexpected token is encountered.
pub fn unexpected_token(token: &str) -> CompileError {
    CompileError::Parse(format!("unexpected token: {}", token))
}

/// Error when a variable is expected in a binder position.
pub fn expected_variable_in_binder(found: &str) -> CompileError {
    CompileError::Parse(format!(
        "expected variable in binder position, found {}",
        found
    ))
}

/// Error when a deprecated LaTeX-style operator is used.
pub fn latex_operator_deprecated(operator: &str, replacement: &str) -> CompileError {
    let ctx = ErrorContext::new()
        .with_help(format!("use '{}' instead", replacement));
    CompileError::parse_with_context(
        format!("LaTeX-style operator '{}' is deprecated", operator),
        ctx,
    )
}

// ============================================
// Result / Option Errors
// ============================================

/// Error when unwrap() is called on None.
pub fn unwrap_on_none() -> CompileError {
    CompileError::Runtime("called unwrap() on a None value".to_string())
}

/// Error when unwrap() is called on Err.
pub fn unwrap_on_err(error: &impl std::fmt::Debug) -> CompileError {
    CompileError::Runtime(format!("called unwrap() on an Err value: {:?}", error))
}

/// Error when unwrap_err() is called on Ok.
pub fn unwrap_err_on_ok(value: &impl std::fmt::Debug) -> CompileError {
    CompileError::Runtime(format!("called unwrap_err() on an Ok value: {:?}", value))
}

/// Error when expect() is called and the value is None/Err.
pub fn expect_failed(message: &str) -> CompileError {
    CompileError::Runtime(format!("expect() failed: {}", message))
}

// ============================================
// Math Eval Errors
// ============================================

/// Error when an undefined variable is used in a math expression.
pub fn undefined_math_variable(var_name: &str) -> CompileError {
    CompileError::Semantic(format!("undefined variable in math expression: '{}'", var_name))
}

/// Error when an unknown function is called in a math expression.
pub fn unknown_math_function(func_name: &str) -> CompileError {
    CompileError::Semantic(format!("unknown function in math expression: '{}'", func_name))
}

/// Error when a 1D tensor index is out of bounds.
pub fn tensor_1d_index_out_of_bounds(index: usize, length: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor index {} out of bounds for 1D tensor of length {}",
        index, length
    ))
}

/// Error when a tensor shape is invalid.
pub fn invalid_tensor_shape(reason: &str) -> CompileError {
    CompileError::Semantic(format!("invalid tensor shape: {}", reason))
}

// ============================================
// Conversion / Parse Errors
// ============================================

/// Error when a value cannot be converted between types.
pub fn cannot_convert(value: &impl std::fmt::Debug, from_type: &str, to_type: &str) -> CompileError {
    CompileError::Semantic(format!(
        "cannot convert {:?} from '{}' to '{}'",
        value, from_type, to_type
    ))
}

/// Error when a socket address is invalid.
pub fn invalid_socket_address(address: &str, reason: &str) -> CompileError {
    CompileError::Semantic(format!(
        "invalid socket address '{}': {}",
        address, reason
    ))
}

/// Error when a configuration value is invalid.
pub fn invalid_config(key: &str, reason: &str) -> CompileError {
    CompileError::Semantic(format!("invalid configuration for '{}': {}", key, reason))
}

// ============================================
// Dependency / Resolution Errors
// ============================================

/// Error when circular dependencies are detected.
pub fn circular_dependency(cycle: &str) -> CompileError {
    CompileError::Semantic(format!("circular dependency detected: {}", cycle))
}

/// Error when a class is not found.
pub fn class_not_found(class_name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::UNKNOWN_CLASS);
    CompileError::semantic_with_context(format!("class '{}' not found", class_name), ctx)
}

/// Error when a wildcard import is used with a strong enum.
pub fn strong_enum_no_wildcard(enum_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "strong enum '{}' cannot be imported with a wildcard; list variants explicitly",
        enum_name
    ))
}

/// Error when a value is not callable.
pub fn not_callable(type_name: &str) -> CompileError {
    CompileError::Semantic(format!("value of type '{}' is not callable", type_name))
}

/// Error when a trait method is not implemented.
pub fn missing_trait_method(trait_name: &str, method_name: &str, type_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "type '{}' does not implement trait method '{}' required by '{}'",
        type_name, method_name, trait_name
    ))
}

/// Error when a trait method is not found.
pub fn trait_method_not_found(trait_name: &str, method_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "trait '{}' has no method named '{}'",
        trait_name, method_name
    ))
}

/// Error when a trait inner type is not an object.
pub fn trait_inner_not_object(trait_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "trait '{}' inner type must be an object type",
        trait_name
    ))
}

/// Error when mock.expects() is not given a method name.
pub fn mock_expects_method_name() -> CompileError {
    CompileError::Semantic("mock.expects() requires a method name argument".to_string())
}

/// Error when mock.verify() is required but not called.
pub fn mock_requires_verify() -> CompileError {
    CompileError::Semantic("mock object requires verify() to be called at end of test".to_string())
}

/// Error when trait coherence rules are violated.
pub fn trait_coherence_errors(details: &str) -> CompileError {
    CompileError::Semantic(format!("trait coherence violation: {}", details))
}

/// Error when an effect violates capability restrictions.
pub fn effect_violates_capabilities(effect: &str, capability: &str) -> CompileError {
    CompileError::Semantic(format!(
        "effect '{}' violates capability restriction '{}'",
        effect, capability
    ))
}

/// Error when an unknown enum variant or method is used.
pub fn unknown_enum_variant_or_method(enum_name: &str, name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "unknown variant or method '{}' on enum '{}'",
        name, enum_name
    ))
}

/// Error when Lean proof runner fails.
pub fn lean_run_failed(reason: &str) -> CompileError {
    CompileError::Semantic(format!("Lean proof runner failed: {}", reason))
}

/// Error when writing a Lean proof file fails.
pub fn lean_write_failed(reason: &str) -> CompileError {
    CompileError::Semantic(format!("failed to write Lean proof file: {}", reason))
}

/// Error when an enum is not found.
pub fn enum_not_found(enum_name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::UNKNOWN_ENUM);
    CompileError::semantic_with_context(format!("enum '{}' not found", enum_name), ctx)
}

// ============================================
// Block / Custom Syntax Errors
// ============================================

/// Error when an unknown block type is encountered.
pub fn unknown_block_type(block_type: &str) -> CompileError {
    CompileError::Semantic(format!("unknown block type: '{}'", block_type))
}

// ============================================
// FFI / Interpreter Errors
// ============================================

/// Error when an expression index is invalid in FFI context.
pub fn invalid_expression_index(index: usize) -> CompileError {
    CompileError::Semantic(format!("invalid expression index {} in FFI context", index))
}

/// Error when an argument must be a socket address.
pub fn argument_must_be_socket_address(index: usize) -> CompileError {
    CompileError::Semantic(format!("argument {} must be a socket address", index))
}

/// Error from an explicit panic with a message.
pub fn panic_with_message(message: &str) -> CompileError {
    CompileError::Runtime(format!("explicit panic: {}", message))
}

/// Error when a cast between incompatible types is attempted.
pub fn cannot_cast_type(from_type: &str, to_type: &str) -> CompileError {
    CompileError::Semantic(format!("cannot cast '{}' to '{}'", from_type, to_type))
}

/// Error when a function is not marked for verification.
pub fn function_not_verify_marked(func_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "function '{}' is not marked with @verify",
        func_name
    ))
}

/// Error when an unknown type ID is encountered.
pub fn unknown_type_id(type_id: u64) -> CompileError {
    CompileError::Semantic(format!("unknown type id: {}", type_id))
}

/// Error when macro expansion exceeds the depth limit.
pub fn macro_expansion_depth_exceeded(limit: usize) -> CompileError {
    CompileError::Semantic(format!(
        "macro expansion depth exceeded limit of {}",
        limit
    ))
}

/// Error when tensor shapes cannot be broadcast together.
pub fn tensor_cannot_broadcast_shapes(left: &str, right: &str) -> CompileError {
    CompileError::Semantic(format!(
        "cannot broadcast tensor shapes {} and {}",
        left, right
    ))
}

/// Error when a tensor axis index is out of bounds.
pub fn tensor_axis_out_of_bounds(axis: usize, rank: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor axis {} is out of bounds for rank-{} tensor",
        axis, rank
    ))
}

/// Error from input/read operations.
pub fn input_error(reason: &str) -> CompileError {
    CompileError::Runtime(format!("input error: {}", reason))
}

/// Error when an unsupported constant type is encountered.
pub fn unsupported_constant_type(type_name: &str) -> CompileError {
    CompileError::Codegen(format!("unsupported constant type: '{}'", type_name))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen_errors() {
        let err = unsupported_feature("SIMD intrinsics");
        assert!(err.to_string().contains("unsupported feature: SIMD intrinsics"));

        let err = undefined_reference("__some_symbol");
        assert!(err.to_string().contains("undefined reference to '__some_symbol'"));
    }

    #[test]
    fn test_assignment_errors() {
        let err = cannot_assign_to_const("MAX_SIZE");
        assert!(err.to_string().contains("cannot assign to immutable binding 'MAX_SIZE'"));

        let err = cannot_mutate_immutable("x");
        assert!(err.to_string().contains("cannot mutate immutable value 'x'"));
    }

    #[test]
    fn test_tensor_errors() {
        let err = tensor_shape_mismatch("add", "[2,3]", "[3,2]");
        assert!(err.to_string().contains("tensor shape mismatch in 'add'"));

        let err = tensor_item_requires_scalar("[2,3]");
        assert!(err.to_string().contains("scalar tensor"));
    }

    #[test]
    fn test_parser_errors() {
        let err = expected_token("')'", "';'");
        assert!(err.to_string().contains("expected ')'"));

        let err = unexpected_token("&&");
        assert!(err.to_string().contains("unexpected token: &&"));
    }

    #[test]
    fn test_runtime_errors() {
        let err = unwrap_on_none();
        assert!(err.to_string().contains("None"));

        let err = panic_with_message("something went wrong");
        assert!(err.to_string().contains("something went wrong"));
    }

    #[test]
    fn test_dependency_errors() {
        let err = circular_dependency("A -> B -> A");
        assert!(err.to_string().contains("circular dependency"));

        let err = not_callable("Int");
        assert!(err.to_string().contains("not callable"));
    }
}
