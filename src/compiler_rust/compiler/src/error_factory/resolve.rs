//! Factory functions: module resolution, arguments, macros, type/name resolution,
//! trait impl, effect/capability, type mismatch, binding, FFI, pipeline/lowering.

use crate::error::{codes, typo, CompileError, ErrorContext};
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
