//! Error factory: tensor, codegen operations, runtime, trait, effect, misc errors.
//!
//! Used via `crate::error::factory::*`.

use crate::error::{codes, CompileError, ErrorContext};

/// Error when unknown local index is accessed.
pub fn llvm_unknown_local(index: usize) -> CompileError {
    CompileError::Semantic(format!("Unknown local index: {}", index))
}

/// Error when undefined virtual register is used.
pub fn llvm_undefined_vreg(vreg: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Undefined vreg: {:?}", vreg))
}

/// Error when a type is unsupported in LLVM backend.
pub fn unsupported_llvm_type(ty: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Unsupported LLVM type: {:?}", ty))
}

/// Error when a type cast is unsupported.
pub fn unsupported_cast(from: &impl std::fmt::Debug, to: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Unsupported cast from {:?} to {:?}", from, to))
}

/// Error when an expected value type is not found.
pub fn expected_value_type(expected: &str, context: &str) -> CompileError {
    CompileError::Semantic(format!("Expected {} value for {}", expected, context))
}

/// Error when LLVM return type is unsupported.
pub fn unsupported_return_type() -> CompileError {
    CompileError::Semantic("Unsupported return type".to_string())
}

/// Error when failed to create LLVM target machine.
pub fn llvm_target_machine_failed() -> CompileError {
    CompileError::Semantic("Failed to create target machine".to_string())
}

/// Error when data has invalid encoding.
pub fn invalid_encoding(context: &str, error: &impl std::fmt::Display) -> CompileError {
    CompileError::Semantic(format!("Invalid encoding in {}: {}", context, error))
}

// ============================================
// Assignment/Mutation Errors
// ============================================

/// Error when trying to assign to a constant.
pub fn cannot_assign_to_const(name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT);
    CompileError::semantic_with_context(format!("cannot assign to const '{}'", name), ctx)
}

/// Error when trying to mutate an immutable value.
pub fn cannot_mutate_immutable(name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT);
    CompileError::semantic_with_context(format!("cannot mutate immutable value '{}'", name), ctx)
}

// ============================================
// Tensor/Math Errors
// ============================================

/// Error when tensor shapes don't match for an operation.
pub fn tensor_shape_mismatch(operation: &str, details: &str) -> CompileError {
    CompileError::Semantic(format!("{} shape mismatch: {}", operation, details))
}

/// Error when tensor cannot be reshaped.
pub fn tensor_reshape_failed(current_size: usize, new_shape: &[usize]) -> CompileError {
    CompileError::Semantic(format!(
        "cannot reshape tensor of size {} to {:?}",
        current_size, new_shape
    ))
}

/// Error when tensor dimension is out of range.
pub fn tensor_dim_out_of_range(dim: usize, ndims: usize) -> CompileError {
    CompileError::Semantic(format!("dimension {} out of range for tensor with {} dims", dim, ndims))
}

/// Error when tensor index is out of bounds.
pub fn tensor_index_out_of_bounds(index: usize, dim: usize, size: usize) -> CompileError {
    CompileError::Semantic(format!(
        "index {} out of bounds for dimension {} with size {}",
        index, dim, size
    ))
}

/// Error when wrong number of indices are provided.
pub fn tensor_index_count_mismatch(expected: usize, found: usize) -> CompileError {
    CompileError::Semantic(format!("expected {} indices, got {}", expected, found))
}

/// Error when tensor data length doesn't match shape.
pub fn tensor_data_length_mismatch(data_len: usize, shape: &[usize], expected: usize) -> CompileError {
    CompileError::Semantic(format!(
        "tensor data length {} doesn't match shape {:?} (expected {})",
        data_len, shape, expected
    ))
}

/// Error when item() is called on non-scalar tensor.
pub fn tensor_item_requires_scalar(actual_len: usize) -> CompileError {
    CompileError::Semantic(format!(
        "item() requires exactly one element, tensor has {}",
        actual_len
    ))
}

// ============================================
// Unit Conversion Errors
// ============================================

/// Error when a unit does not belong to a family.
pub fn unit_no_family(unit_suffix: &str, target_suffix: &str) -> CompileError {
    CompileError::Semantic(format!(
        "Unit '{}' does not belong to a unit family, cannot convert to '{}'",
        unit_suffix, target_suffix
    ))
}

/// Error when a unit family is not found.
///
/// Defensively triggers a lazy load of the on-disk unit catalog
/// (`src/unit/simple-lang/`) before producing the error so any future caller
/// benefits from the registry without needing its own seed call. The seeding
/// is idempotent per thread.
pub fn unit_family_not_found(family: &str) -> CompileError {
    crate::units::ensure_loaded();
    CompileError::Semantic(format!("Unit family '{}' not found", family))
}

/// Error when a unit is not found in a family.
pub fn unit_not_in_family(unit_suffix: &str, family: &str) -> CompileError {
    CompileError::Semantic(format!("Unit '{}' not found in family '{}'", unit_suffix, family))
}

/// Error when a target unit is not found for conversion.
pub fn target_unit_not_found(target: &str, family: &str, available: &str) -> CompileError {
    CompileError::Semantic(format!(
        "Target unit '{}' not found in family '{}'. Available: {}",
        target, family, available
    ))
}

/// Error when converting a non-numeric unit value.
pub fn unit_non_numeric_conversion(value: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Cannot convert non-numeric unit value: {:?}", value))
}

// ============================================
// Parser Errors
// ============================================

/// Error when an expected token is not found.
pub fn expected_token(expected: &impl std::fmt::Debug, found: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("expected {:?}, found {:?}", expected, found))
}

/// Error when an unexpected token is encountered.
pub fn unexpected_token(context: &str, token: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("unexpected token in {}: {:?}", context, token))
}

/// Error when a variable name is expected in a binder.
pub fn expected_variable_in_binder() -> CompileError {
    CompileError::Semantic("expected variable name in binder".to_string())
}

/// Error when a LaTeX operator should be replaced.
pub fn latex_operator_deprecated(cmd: &str) -> CompileError {
    CompileError::Semantic(format!("LaTeX operator \\{} should be replaced with *", cmd))
}

// ============================================
// Result/Option Errors
// ============================================

/// Error when unwrap is called on None.
pub fn unwrap_on_none() -> CompileError {
    CompileError::Semantic("called unwrap on None".to_string())
}

/// Error when unwrap is called on Err.
pub fn unwrap_on_err(payload: Option<&str>) -> CompileError {
    match payload {
        Some(msg) => CompileError::Semantic(format!("called unwrap on Err: {}", msg)),
        None => CompileError::Semantic("called unwrap on Err".to_string()),
    }
}

/// Error when unwrap_err is called on Ok.
pub fn unwrap_err_on_ok() -> CompileError {
    CompileError::Semantic("called unwrap_err on Ok".to_string())
}

/// Error for expect with a custom message.
pub fn expect_failed(message: &str, payload: Option<&str>) -> CompileError {
    match payload {
        Some(p) => CompileError::Semantic(format!("{}: {}", message, p)),
        None => CompileError::Semantic(message.to_string()),
    }
}

// ============================================
// Math Evaluation Errors
// ============================================

/// Error when a math variable is undefined.
pub fn undefined_math_variable(name: &str) -> CompileError {
    CompileError::Semantic(format!("undefined math variable: {}", name))
}

/// Error when a math function is unknown.
pub fn unknown_math_function(name: &str) -> CompileError {
    CompileError::Semantic(format!("unknown math function: {}", name))
}

/// Error when a tensor index is out of bounds for a 1D tensor.
pub fn tensor_1d_index_out_of_bounds(index: usize, length: usize) -> CompileError {
    CompileError::Semantic(format!("index {} out of bounds for tensor of length {}", index, length))
}

/// Error when a tensor shape argument is invalid.
pub fn invalid_tensor_shape() -> CompileError {
    CompileError::Semantic("invalid tensor shape: dimensions must be positive integers".to_string())
}

// ============================================
// Conversion/Parse Errors
// ============================================

/// Error when a value cannot be converted to a target type.
pub fn cannot_convert(value: &str, target_type: &str) -> CompileError {
    CompileError::Semantic(format!("cannot convert '{}' to {}", value, target_type))
}

/// Error when a string cannot be parsed as a socket address.
pub fn invalid_socket_address(addr: &str) -> CompileError {
    CompileError::Semantic(format!("invalid socket address: {}", addr))
}

/// Error when a config/manifest file is invalid.
pub fn invalid_config(kind: &str, error: &impl std::fmt::Display) -> CompileError {
    CompileError::Semantic(format!("invalid {}: {}", kind, error))
}

// ============================================
// Dependency/Resolution Errors
// ============================================

/// Error when a circular dependency is detected.
pub fn circular_dependency(description: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::CIRCULAR_DEPENDENCY);
    CompileError::semantic_with_context(format!("circular dependency detected: {}", description), ctx)
}

/// Error when a class is not found.
pub fn class_not_found(class_name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::UNKNOWN_CLASS);
    CompileError::semantic_with_context(format!("unknown class '{}'", class_name), ctx)
}

/// Error when a strong enum has wildcard pattern in match.
pub fn strong_enum_no_wildcard(enum_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "strong enum '{}' does not allow wildcard or catch-all patterns in match",
        enum_name
    ))
}

/// Error when a value is not callable.
pub fn not_callable(type_name: &str) -> CompileError {
    CompileError::Semantic(format!("cannot call value of type {}", type_name))
}

/// Error when a required trait method is not implemented.
pub fn missing_trait_method(type_name: &str, method_name: &str, trait_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "type `{}` does not implement required method `{}` from trait `{}`",
        type_name, method_name, trait_name
    ))
}

/// Error when method not found on trait object.
pub fn trait_method_not_found(method: &str, trait_name: &str, type_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "Method '{}' not found on dyn {} (type: {})",
        method, trait_name, type_name
    ))
}

/// Error when calling method on non-object trait value.
pub fn trait_inner_not_object(method: &str, trait_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "Cannot call method '{}' on dyn {}: inner value is not an object",
        method, trait_name
    ))
}

/// Error when mock method expects symbol or string.
pub fn mock_expects_method_name(context: &str) -> CompileError {
    CompileError::Semantic(format!("{} expects symbol or string method name", context))
}

/// Error when mock method must be chained after verify.
pub fn mock_requires_verify(context: &str) -> CompileError {
    CompileError::Semantic(format!("{}() must be chained after verify(:method)", context))
}

/// Error for trait coherence violations.
pub fn trait_coherence_errors(errors: &[String]) -> CompileError {
    CompileError::Semantic(format!("Trait coherence errors:\n{}", errors.join("\n")))
}

/// Error when function effect violates module capabilities.
pub fn effect_violates_capabilities(func_name: &str, effect: &str, allowed_caps: &str, cap_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "function '{}' has @{} effect but module only allows capabilities: [{}]\n\
         help: add '{}' to module's 'requires [...]' statement or remove @{} from function",
        func_name, effect, allowed_caps, cap_name, effect
    ))
}

/// Error when an unknown variant or method on enum.
pub fn unknown_enum_variant_or_method(method: &str, enum_name: &str) -> CompileError {
    CompileError::Semantic(format!("unknown variant or method '{}' on enum {}", method, enum_name))
}

/// Error when running Lean fails.
pub fn lean_run_failed(error: &impl std::fmt::Display) -> CompileError {
    CompileError::Semantic(format!("Failed to run Lean: {}", error))
}

/// Error when writing Lean file fails.
pub fn lean_write_failed(error: &impl std::fmt::Display) -> CompileError {
    CompileError::Semantic(format!("Failed to write Lean file: {}", error))
}

/// Error when an enum is not found.
pub fn enum_not_found(enum_name: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::UNKNOWN_ENUM);
    CompileError::semantic_with_context(format!("unknown enum '{}'", enum_name), ctx)
}

// ============================================
// Block/Custom Syntax Errors
// ============================================

/// Error when an unknown block type is used.
pub fn unknown_block_type(kind: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::UNKNOWN_BLOCK_TYPE);
    CompileError::semantic_with_context(format!("unknown block kind: {}", kind), ctx)
}

// ============================================
// FFI/Interpreter Errors
// ============================================

/// Error when an expression index is invalid.
pub fn invalid_expression_index(index: usize) -> CompileError {
    CompileError::Semantic(format!("invalid expression index: {}", index))
}

/// Error when an argument must be a socket address.
pub fn argument_must_be_socket_address(idx: usize) -> CompileError {
    CompileError::Semantic(format!("argument {} must be a socket address", idx))
}

/// Error for panic with message.
pub fn panic_with_message(msg: &str) -> CompileError {
    CompileError::Semantic(format!("panic: {}", msg))
}

/// Error when a type cannot be cast.
pub fn cannot_cast_type(from_type: &str, to_type: &str) -> CompileError {
    CompileError::Semantic(format!("cannot cast {} to {}", from_type, to_type))
}

/// Error when a function is not marked @verify.
pub fn function_not_verify_marked(func_name: &str) -> CompileError {
    CompileError::Semantic(format!("Function '{}' is not marked @verify", func_name))
}

/// Error when an unknown type ID is encountered.
pub fn unknown_type_id(type_id: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Unknown type ID: {:?}", type_id))
}

/// Error when macro expansion depth is exceeded.
pub fn macro_expansion_depth_exceeded(max: usize, macro_name: &str) -> CompileError {
    CompileError::Semantic(format!(
        "macro expansion depth exceeded maximum of {} (recursive macro invocation of '{}')",
        max, macro_name
    ))
}

/// Error when tensor shapes cannot be broadcast.
pub fn tensor_cannot_broadcast_shapes(a: &[usize], b: &[usize]) -> CompileError {
    CompileError::Semantic(format!("cannot broadcast shapes {:?} and {:?}", a, b))
}

/// Error when axis is out of bounds for tensor.
pub fn tensor_axis_out_of_bounds(axis: usize, ndims: usize) -> CompileError {
    CompileError::Semantic(format!(
        "axis {} out of bounds for tensor with {} dimensions",
        axis, ndims
    ))
}

/// Error for input reading errors.
pub fn input_error(e: &impl std::fmt::Display) -> CompileError {
    CompileError::Semantic(format!("input error: {}", e))
}

/// Error when a constant type is unsupported in test helpers.
pub fn unsupported_constant_type(ty: &impl std::fmt::Debug) -> CompileError {
    CompileError::Semantic(format!("Unsupported constant type for test helper: {:?}", ty))
}
