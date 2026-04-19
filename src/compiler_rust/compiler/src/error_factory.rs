/// Error factory functions for common error patterns.
///
/// This module provides constructor functions for frequently-used error messages,
/// reducing duplication and ensuring consistent error text across the codebase.
pub mod factory {
    use super::{codes, typo, CompileError, ErrorContext};
    use std::path::Path;

    // ============================================
    // Module Resolution Errors
    // ============================================

    /// Error when a module cannot be resolved from an import path.
    pub fn cannot_resolve_module(module_name: &str) -> CompileError {
        CompileError::Semantic(format!("Cannot resolve module: {}", module_name))
    }

    /// Error when a module file cannot be read from disk.
    pub fn cannot_read_module(path: &Path, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Io(format!("Cannot read module {:?}: {}", path, error))
    }

    /// Error when a module file fails to parse.
    pub fn cannot_parse_module(path: &Path, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Parse(format!("Cannot parse module {:?}: {}", path, error))
    }

    /// Error when a module is not found at the expected path.
    pub fn module_not_found(module_name: &str, searched_paths: &[&Path]) -> CompileError {
        let paths_str = searched_paths
            .iter()
            .map(|p| format!("  - {:?}", p))
            .collect::<Vec<_>>()
            .join("\n");
        CompileError::Semantic(format!(
            "Module '{}' not found. Searched paths:\n{}",
            module_name, paths_str
        ))
    }

    /// Error when a file cannot be read.
    pub fn failed_to_read_file(path: &impl std::fmt::Debug, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("failed to read {:?}: {}", path, error))
    }

    /// Error when a file fails to parse.
    pub fn failed_to_parse_file(filename: &str, error: &impl std::fmt::Debug) -> CompileError {
        CompileError::Semantic(format!("failed to parse {}: {:?}", filename, error))
    }

    /// Error when module capabilities are not a subset of parent capabilities.
    pub fn capability_violation(module_name: &str, child_caps: &str, parent_caps: &str) -> CompileError {
        CompileError::Semantic(format!(
            "module '{}' declares capabilities [{}] which are not a subset of parent capabilities [{}]",
            module_name, child_caps, parent_caps
        ))
    }

    // ============================================
    // Argument/Type Errors
    // ============================================

    /// Error when a function argument has an unexpected type.
    pub fn argument_type_mismatch(index: usize, expected: &str, found: &str) -> CompileError {
        CompileError::Semantic(format!("argument {} must be {}, found {}", index, expected, found))
    }

    /// Error when a function receives the wrong number of arguments.
    pub fn argument_count_mismatch(expected: usize, found: usize) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH);
        CompileError::semantic_with_context(format!("expected {} argument(s), found {}", expected, found), ctx)
    }

    /// Error when a function expects a minimum number of arguments.
    pub fn func_expects_args(func_name: &str, expected: usize, found: usize) -> CompileError {
        CompileError::Semantic(format!("{} expects {} argument(s), got {}", func_name, expected, found))
    }

    /// Error when a function expects at least N arguments.
    pub fn func_expects_at_least(func_name: &str, min: usize, found: usize) -> CompileError {
        CompileError::Semantic(format!(
            "{} expects at least {} argument(s), got {}",
            func_name, min, found
        ))
    }

    /// Error when a function argument has the wrong type (with func name).
    pub fn func_expects_type_at(func_name: &str, expected_type: &str, index: usize) -> CompileError {
        CompileError::Semantic(format!(
            "{} expects {} argument at position {}",
            func_name, expected_type, index
        ))
    }

    /// Error when a required argument is missing.
    pub fn missing_argument(name: &str) -> CompileError {
        CompileError::Semantic(format!("missing required argument: {}", name))
    }

    /// Error when an argument must be a specific type (simpler version).
    pub fn argument_must_be(index: usize, expected_type: &str) -> CompileError {
        CompileError::Semantic(format!("argument {} must be {}", index, expected_type))
    }

    /// Error when an operation expects a lambda argument.
    pub fn expects_lambda(operation: &str) -> CompileError {
        CompileError::Semantic(format!("{} expects lambda argument", operation))
    }

    /// Error when a const binding has wrong type.
    pub fn const_binding_wrong_type(name: &str, expected: &str, found: &str) -> CompileError {
        CompileError::Semantic(format!("Const binding '{}' is not {}: {}", name, expected, found))
    }

    /// Error when a const binding is not found.
    pub fn const_binding_not_found(name: &str) -> CompileError {
        CompileError::Semantic(format!("Const binding '{}' not found", name))
    }

    // ============================================
    // Macro Errors
    // ============================================

    /// Error when an unknown macro is invoked.
    pub fn unknown_macro(name: &str) -> CompileError {
        CompileError::Semantic(format!("unknown macro: {}!", name))
    }

    /// Error when a macro is used before its definition.
    pub fn macro_used_before_definition(name: &str) -> CompileError {
        CompileError::Semantic(format!("macro '{}' used before definition", name))
    }

    /// Error when a macro invocation fails.
    pub fn macro_invocation_failed(name: &str, reason: &str) -> CompileError {
        CompileError::Semantic(format!("macro '{}' invocation failed: {}", name, reason))
    }

    /// Error when a panic! macro is invoked.
    pub fn panic_macro(message: &str) -> CompileError {
        CompileError::Semantic(format!("panic: {}", message))
    }

    /// Error when an assertion fails.
    pub fn assertion_failed(left: &impl std::fmt::Debug, right: &impl std::fmt::Debug) -> CompileError {
        CompileError::Semantic(format!("assertion failed: {:?} != {:?}", left, right))
    }

    /// Error when a unit assertion fails.
    pub fn unit_assertion_failed(error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("unit assertion failed: {}", error))
    }

    /// Error when a type is not a valid unit type.
    pub fn invalid_unit_type(type_name: &str) -> CompileError {
        CompileError::Semantic(format!(
            "assert_unit: '{}' is not a registered unit type (family or compound unit)",
            type_name
        ))
    }

    // ============================================
    // Type/Name Resolution Errors
    // ============================================

    /// Error when a type is not found.
    pub fn type_not_found(type_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::UNDEFINED_TYPE);
        CompileError::semantic_with_context(format!("type '{}' not found in this scope", type_name), ctx)
    }

    /// Error when a variable is not found.
    pub fn variable_not_found(var_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::UNDEFINED_VARIABLE);
        CompileError::semantic_with_context(format!("cannot find variable '{}' in this scope", var_name), ctx)
    }

    /// Error when a function is not found.
    pub fn function_not_found(func_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FUNCTION);
        CompileError::semantic_with_context(format!("cannot find function '{}' in this scope", func_name), ctx)
    }

    /// Error when a method is not found on a type.
    pub fn method_not_found(method_name: &str, type_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::UNKNOWN_METHOD);
        CompileError::semantic_with_context(
            format!("no method named '{}' found for type '{}'", method_name, type_name),
            ctx,
        )
    }

    /// Error when a field is not found on a struct/class.
    pub fn field_not_found(field_name: &str, type_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FIELD);
        CompileError::semantic_with_context(
            format!("no field named '{}' found on type '{}'", field_name, type_name),
            ctx,
        )
    }

    // ============================================
    // Type/Name Resolution Errors with Suggestions
    // ============================================

    /// Error when a type is not found, with typo suggestions.
    pub fn type_not_found_with_suggestions(type_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNDEFINED_TYPE);

        if let Some(suggestion) = typo::suggest_name(type_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(format!("type '{}' not found in this scope", type_name), ctx)
    }

    /// Error when a variable is not found, with typo suggestions.
    pub fn variable_not_found_with_suggestions(var_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNDEFINED_VARIABLE);

        if let Some(suggestion) = typo::suggest_name(var_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(format!("cannot find variable '{}' in this scope", var_name), ctx)
    }

    /// Error when a function is not found, with typo suggestions.
    pub fn function_not_found_with_suggestions(func_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNDEFINED_FUNCTION);

        if let Some(suggestion) = typo::suggest_name(func_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(format!("cannot find function '{}' in this scope", func_name), ctx)
    }

    /// Error when a method is not found on a type, with typo suggestions.
    pub fn method_not_found_with_suggestions(method_name: &str, type_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNKNOWN_METHOD);

        if let Some(suggestion) = typo::suggest_name(method_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(
            format!("no method named '{}' found for type '{}'", method_name, type_name),
            ctx,
        )
    }

    /// Error when a field is not found on a struct/class, with typo suggestions.
    pub fn field_not_found_with_suggestions(field_name: &str, type_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNDEFINED_FIELD);

        if let Some(suggestion) = typo::suggest_name(field_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(
            format!("no field named '{}' found on type '{}'", field_name, type_name),
            ctx,
        )
    }

    /// Error when a class is not found, with typo suggestions.
    pub fn class_not_found_with_suggestions(class_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNKNOWN_CLASS);

        if let Some(suggestion) = typo::suggest_name(class_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(format!("unknown class '{}'", class_name), ctx)
    }

    /// Error when an enum is not found, with typo suggestions.
    pub fn enum_not_found_with_suggestions(enum_name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::UNKNOWN_ENUM);

        if let Some(suggestion) = typo::suggest_name(enum_name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
        }

        CompileError::semantic_with_context(format!("unknown enum '{}'", enum_name), ctx)
    }

    /// Error when an unknown macro is invoked, with typo suggestions.
    pub fn unknown_macro_with_suggestions(name: &str, candidates: &[&str]) -> CompileError {
        let mut ctx = ErrorContext::new().with_code(codes::MACRO_UNDEFINED);

        if let Some(suggestion) = typo::suggest_name(name, candidates.iter().copied()) {
            ctx = ctx.with_help(format!("did you mean '{}!'?", suggestion));
        }

        CompileError::semantic_with_context(format!("unknown macro: {}!", name), ctx)
    }

    // ============================================
    // Trait Impl Errors
    // ============================================

    /// Error when a default impl must be a blanket impl.
    pub fn default_impl_must_be_blanket(trait_name: &str) -> CompileError {
        CompileError::Semantic(format!(
            "#[default] impl for trait `{}` must be a blanket impl (impl[T] Trait for T)",
            trait_name
        ))
    }

    /// Error when a duplicate blanket impl is found.
    pub fn duplicate_blanket_impl(trait_name: &str) -> CompileError {
        CompileError::Semantic(format!("duplicate blanket impl for trait `{}`", trait_name))
    }

    /// Error when overlapping impls are found.
    pub fn overlapping_impls(trait_name: &str, context: &str) -> CompileError {
        CompileError::Semantic(format!("overlapping impls for trait `{}`: {}", trait_name, context))
    }

    /// Error when a duplicate impl is found for a specific type.
    pub fn duplicate_impl(trait_name: &str, type_name: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::DUPLICATE_DEFINITION);
        CompileError::semantic_with_context(
            format!("duplicate impl for trait `{}` and type `{}`", trait_name, type_name),
            ctx,
        )
    }

    // ============================================
    // Effect/Capability Errors
    // ============================================

    /// Error when a blocking operation is used in async context.
    pub fn blocking_in_async(operation: &str) -> CompileError {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help("remove @async decorator or use non-blocking alternative");
        CompileError::semantic_with_context(
            format!("blocking operation '{}' not allowed in async function", operation),
            ctx,
        )
    }

    /// Error when a side-effecting operation is used in pure context.
    pub fn side_effect_in_pure(operation: &str, needed_effect: &str) -> CompileError {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help(format!(
                "remove @pure decorator or add {} effect to function",
                needed_effect
            ));
        CompileError::semantic_with_context(
            format!("side-effecting operation '{}' not allowed in pure function", operation),
            ctx,
        )
    }

    /// Error when a pure function calls a non-pure function.
    pub fn pure_calls_impure(callee_name: &str, callee_effects: &str) -> CompileError {
        CompileError::Semantic(format!(
            "pure function cannot call '{}' which has effects: {}\n\
             help: remove @pure decorator from caller or add @pure to callee",
            callee_name, callee_effects
        ))
    }

    /// Error when a pure function calls a function with a specific effect.
    pub fn pure_calls_effect(callee_name: &str, effect_name: &str) -> CompileError {
        CompileError::Semantic(format!(
            "pure function cannot call '{}' with @{} effect\n\
             help: remove @pure decorator from caller or remove @{} from callee",
            callee_name, effect_name, effect_name
        ))
    }

    // ============================================
    // Type Mismatch Errors
    // ============================================

    /// Error when two types don't match.
    pub fn type_mismatch(expected: &str, found: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::TYPE_MISMATCH);
        CompileError::semantic_with_context(format!("expected type '{}', found '{}'", expected, found), ctx)
    }

    /// Error when a return type doesn't match the function signature.
    pub fn return_type_mismatch(expected: &str, found: &str) -> CompileError {
        let ctx = ErrorContext::new().with_code(codes::INVALID_RETURN_TYPE);
        CompileError::semantic_with_context(
            format!("return type mismatch: expected '{}', found '{}'", expected, found),
            ctx,
        )
    }

    // ============================================
    // Binding/Variable Errors
    // ============================================

    /// Error when a let binding fails.
    pub fn let_binding_failed(var_name: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("let binding '{}': {}", var_name, error))
    }

    /// Error when an undefined field is accessed.
    pub fn undefined_field(field_name: &str) -> CompileError {
        CompileError::Semantic(format!("undefined field '{}'", field_name))
    }

    // ============================================
    // FFI/Handle Errors
    // ============================================

    /// Error when a handle argument is expected but not provided.
    pub fn expected_handle(index: usize) -> CompileError {
        CompileError::Semantic(format!("argument {} must be a handle", index))
    }

    /// Error when an FFI call returns an invalid handle.
    pub fn invalid_ffi_handle(function_name: &str) -> CompileError {
        CompileError::Semantic(format!("FFI call '{}' returned invalid handle", function_name))
    }

    // ============================================
    // Pipeline/Lowering Errors
    // ============================================

    /// Error when HIR lowering fails.
    pub fn hir_lowering_failed(error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("HIR lowering: {}", error))
    }

    /// Error when MIR lowering fails.
    pub fn mir_lowering_failed(error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("MIR lowering: {}", error))
    }

    /// Error when type checking fails.
    pub fn type_check_failed(error: &impl std::fmt::Debug) -> CompileError {
        CompileError::Semantic(format!("{:?}", error))
    }

    /// Error when verification produces errors.
    pub fn verification_errors(message: &str) -> CompileError {
        CompileError::Semantic(format!("Verification errors:\n{}", message))
    }

    /// Error when ghost erasure produces errors.
    pub fn ghost_erasure_errors(message: &str) -> CompileError {
        CompileError::Semantic(format!("Ghost erasure errors:\n{}", message))
    }

    // ============================================
    // Codegen Errors
    // ============================================

    /// Error when a feature is not supported in the current backend.
    pub fn unsupported_feature(feature: &str) -> CompileError {
        CompileError::Codegen(format!("unsupported feature: {}", feature))
    }

    /// Error when codegen fails for a specific construct.
    pub fn codegen_failed(construct: &str, reason: &str) -> CompileError {
        CompileError::Codegen(format!("failed to generate code for {}: {}", construct, reason))
    }

    /// Error when an operation is not supported.
    pub fn unsupported_operation(op_type: &str, op: &impl std::fmt::Debug) -> CompileError {
        CompileError::Semantic(format!("Unsupported {}: {:?}", op_type, op))
    }

    /// Error when a reference to something undefined is encountered.
    pub fn undefined_reference(kind: &str, value: &impl std::fmt::Debug) -> CompileError {
        CompileError::Semantic(format!("Undefined {}: {:?}", kind, value))
    }

    /// Error when an LLVM build operation fails.
    pub fn llvm_build_failed(operation: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to build {}: {}", operation, error))
    }

    /// Error when an LLVM cast operation fails.
    pub fn llvm_cast_failed(operation: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to {}: {}", operation, error))
    }

    /// Error when LLVM initialization fails.
    pub fn llvm_init_failed(component: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to initialize {}: {}", component, error))
    }

    /// Error when an intrinsic is not declared.
    pub fn intrinsic_not_declared(name: &str) -> CompileError {
        CompileError::Semantic(format!("Intrinsic {} not declared", name))
    }

    /// Error when calling an intrinsic fails.
    pub fn intrinsic_call_failed(name: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to call {} intrinsic: {}", name, error))
    }

    /// Error when an intrinsic returns an unexpected type.
    pub fn intrinsic_unexpected_type(name: &str) -> CompileError {
        CompileError::Semantic(format!("{} intrinsic returned unexpected type", name))
    }

    /// Error when LLVM target acquisition fails.
    pub fn llvm_target_failed(target: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to get {} target: {}", target, error))
    }

    /// Error when LLVM code emission fails.
    pub fn llvm_emit_failed(format: &str, error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("Failed to emit {}: {}", format, error))
    }

    /// Error when LLVM verification fails.
    pub fn llvm_verification_failed(error: &impl std::fmt::Display) -> CompileError {
        CompileError::Semantic(format!("LLVM verification failed: {}", error))
    }

    /// Error when LLVM module is not created.
    pub fn llvm_module_not_created() -> CompileError {
        CompileError::Semantic("Module not created".to_string())
    }

    /// Error when LLVM builder is not created.
    pub fn llvm_builder_not_created() -> CompileError {
        CompileError::Semantic("Builder not created".to_string())
    }

    /// Error when LLVM feature is not enabled.
    pub fn llvm_feature_not_enabled() -> CompileError {
        CompileError::Semantic("LLVM feature not enabled".to_string())
    }

    /// Error when LLVM feature is required with instructions.
    pub fn llvm_feature_required() -> CompileError {
        CompileError::Semantic(
            "LLVM backend requires 'llvm' feature flag. \
             Build with: cargo build --features llvm"
                .to_string(),
        )
    }

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
    pub fn unit_family_not_found(family: &str) -> CompileError {
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
    pub fn effect_violates_capabilities(
        func_name: &str,
        effect: &str,
        allowed_caps: &str,
        cap_name: &str,
    ) -> CompileError {
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

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::path::PathBuf;

        #[test]
        fn test_module_errors() {
            let err = cannot_resolve_module("foo.bar");
            assert!(err.to_string().contains("Cannot resolve module: foo.bar"));

            let path = PathBuf::from("/tmp/test.spl");
            let err = cannot_read_module(&path, &"permission denied");
            assert!(err.to_string().contains("Cannot read module"));
        }

        #[test]
        fn test_argument_errors() {
            let err = argument_type_mismatch(0, "an integer", "a string");
            assert!(err.to_string().contains("argument 0 must be an integer"));

            let err = argument_count_mismatch(3, 2);
            assert!(err.to_string().contains("expected 3 argument(s), found 2"));
        }

        #[test]
        fn test_macro_errors() {
            let err = unknown_macro("foobar");
            assert!(err.to_string().contains("unknown macro: foobar!"));
        }

        #[test]
        fn test_type_errors() {
            let err = type_mismatch("Int", "String");
            assert!(err.to_string().contains("expected type 'Int', found 'String'"));
        }
    }
}
