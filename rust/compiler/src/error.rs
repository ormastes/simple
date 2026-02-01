//! Compiler error types with rich diagnostic support.
//!
//! This module provides error types that can be converted to rich diagnostics
//! with source context, labels, and suggestions.

use crate::value::Value;
use simple_parser::{Diagnostic, Severity, Span};
use thiserror::Error;

/// Error codes for compiler errors.
///
/// Format: E1xxx for semantic, E2xxx for codegen, E3xxx for runtime
pub mod codes {
    // Semantic errors (E10xx)
    pub const UNDEFINED_VARIABLE: &str = "E1001";
    pub const UNDEFINED_FUNCTION: &str = "E1002";
    pub const TYPE_MISMATCH: &str = "E1003";
    pub const INVALID_ASSIGNMENT: &str = "E1004";
    pub const INVALID_OPERATION: &str = "E1005";
    pub const INVALID_PATTERN: &str = "E1006";
    pub const MISSING_FIELD: &str = "E1007";
    pub const DUPLICATE_DEFINITION: &str = "E1008";
    pub const CIRCULAR_DEPENDENCY: &str = "E1009";
    pub const MODULE_NOT_FOUND: &str = "E1010";
    pub const UNDEFINED_TYPE: &str = "E1011";
    pub const UNDEFINED_FIELD: &str = "E1012";
    pub const UNKNOWN_METHOD: &str = "E1013";
    pub const UNKNOWN_CLASS: &str = "E1014";
    pub const UNKNOWN_ENUM: &str = "E1015";
    pub const LET_BINDING_FAILED: &str = "E1016";
    pub const IMPURE_FUNCTION_IN_CONTRACT: &str = "E1017";
    pub const EFFECT_DECLARATION_FAILED: &str = "E1018";
    pub const DUPLICATE_BINDING: &str = "E1019";
    pub const ARGUMENT_COUNT_MISMATCH: &str = "E1020";
    pub const MISSING_STRUCT_FIELDS: &str = "E1021";
    pub const INVALID_LHS_ASSIGNMENT: &str = "E1022";
    pub const INVALID_STRUCT_LITERAL: &str = "E1023";
    pub const CONST_EVAL_FAILED: &str = "E1024";
    pub const DUPLICATE_METHOD: &str = "E1025";
    pub const UNKNOWN_ASSOC_TYPE: &str = "E1026";
    pub const UNCONSTRAINED_TYPE_PARAM: &str = "E1027";
    pub const UNKNOWN_ASSOC_TYPE_NAME: &str = "E1028";
    pub const CONFLICTING_TRAIT_BOUNDS: &str = "E1029";
    pub const INVALID_LIFETIME_ON_TRAIT: &str = "E1030";
    pub const MISSING_TRAIT_METHOD: &str = "E1031";
    pub const SELF_IN_STATIC: &str = "E1032";
    pub const INVALID_SELF_IMPORT: &str = "E1033";
    pub const UNRESOLVED_IMPORT: &str = "E1034";
    pub const INVALID_SELF_CONTEXT: &str = "E1035";
    pub const CLOSURE_CAPTURE_FAILED: &str = "E1036";
    pub const INVALID_SELF_PARAM: &str = "E1037";
    pub const PRIVATE_IN_PUBLIC: &str = "E1038";
    pub const INVALID_VISIBILITY: &str = "E1039";
    pub const PRIVATE_FIELD_ACCESS: &str = "E1040";
    pub const INVALID_UNARY_OP: &str = "E1041";
    pub const INVALID_SELF_TYPE: &str = "E1042";
    pub const INVALID_INDEX_TYPE: &str = "E1043";
    pub const TUPLE_INDEX_OOB: &str = "E1044";
    pub const INVALID_FIELD_ASSIGN: &str = "E1045";
    pub const PRIVATE_FIELD: &str = "E1046";
    pub const CANNOT_BORROW_MUT_FIELD: &str = "E1047";
    pub const NOT_CALLABLE: &str = "E1048";
    pub const CANNOT_CALL_NON_FUNCTION: &str = "E1049";
    pub const DISALLOWED_COERCION: &str = "E1050";
    pub const CLOSURE_SIGNATURE_MISMATCH: &str = "E1051";
    pub const INVALID_LET_ELSE_PATTERN: &str = "E1052";
    pub const CANNOT_BORROW_IMMUTABLE: &str = "E1053";
    pub const INVALID_DEREFERENCE: &str = "E1054";
    pub const TYPE_ALIAS_BOUNDS: &str = "E1055";
    pub const INVALID_RANGE: &str = "E1056";
    pub const YIELD_OUTSIDE_GENERATOR: &str = "E1057";
    pub const INVALID_DOC_COMMENT: &str = "E1058";
    pub const INVALID_IMPLICIT_DEREFERENCE: &str = "E1059";
    pub const INVALID_CONST_EXPRESSION: &str = "E1060";
    pub const EMPTY_ENUM: &str = "E1061";
    pub const RECURSION_LIMIT_EXCEEDED: &str = "E1062";
    pub const TYPE_SIZE_LIMIT_EXCEEDED: &str = "E1063";
    pub const WRONG_INTRINSIC_TYPE: &str = "E1064";
    pub const INVALID_RETURN_TYPE: &str = "E1065";
    pub const INVALID_MAIN_SIGNATURE: &str = "E1066";
    pub const INVALID_BUILTIN_ATTRIBUTE: &str = "E1067";
    pub const INCONSISTENT_BINDINGS: &str = "E1068";
    pub const MISMATCHED_BINDING: &str = "E1069";
    pub const INVALID_DEFAULT_VARIANT: &str = "E1070";
    pub const INVALID_ATTRIBUTE_POSITION: &str = "E1071";
    pub const INVALID_DESTRUCTURING: &str = "E1072";
    pub const NON_EXHAUSTIVE_TYPE: &str = "E1073";
    pub const CONFLICTING_REPRESENTATION: &str = "E1074";
    pub const DISCRIMINANT_OVERFLOW: &str = "E1075";
    pub const UNKNOWN_INTRINSIC: &str = "E1076";
    pub const WRONG_INTRINSIC_SIGNATURE: &str = "E1077";
    pub const INVALID_INTRINSIC_RETURN: &str = "E1078";
    pub const MISSING_GENERIC_ARGUMENTS: &str = "E1079";
    pub const TYPE_TOO_COMPLEX: &str = "E1080";

    // Control flow errors (E11xx)
    pub const BREAK_OUTSIDE_LOOP: &str = "E1101";
    pub const CONTINUE_OUTSIDE_LOOP: &str = "E1102";
    pub const RETURN_OUTSIDE_FUNCTION: &str = "E1103";
    pub const RETURN_IN_CLOSURE: &str = "E1104";
    pub const INVALID_CONTROL_FLOW: &str = "E1105";

    // Actor/concurrency errors (E12xx)
    pub const ACTOR_SEND_FAILED: &str = "E1201";
    pub const ACTOR_RECV_FAILED: &str = "E1202";
    pub const CHANNEL_CLOSED: &str = "E1203";
    pub const DEADLOCK_DETECTED: &str = "E1204";
    pub const ACTOR_JOIN_FAILED: &str = "E1205";

    // Context errors (E10xx continued)
    pub const INVALID_CONTEXT: &str = "E1081";

    // Capability errors (E13xx)
    pub const CAPABILITY_VIOLATION: &str = "E1301";
    pub const ISOLATION_VIOLATION: &str = "E1302";
    pub const BORROW_VIOLATION: &str = "E1303";
    pub const USE_AFTER_FREE: &str = "E1304";

    // Macro errors (E14xx)
    pub const MACRO_UNDEFINED: &str = "E1401";
    pub const MACRO_USED_BEFORE_DEFINITION: &str = "E1402";
    pub const KEYWORD_IN_MACRO: &str = "E1403";
    pub const MACRO_SHADOWING: &str = "E1403"; // Alias for backward compatibility
    pub const MACRO_INVALID_BLOCK_POSITION: &str = "E1404";
    pub const MACRO_MISSING_TYPE_ANNOTATION: &str = "E1405";
    pub const MACRO_INVALID_QIDENT: &str = "E1406";

    // AOP errors (E15xx)
    pub const INVALID_POINTCUT_SYNTAX: &str = "E1501";
    pub const UNDEFINED_JOINPOINT: &str = "E1502";
    pub const INVALID_ADVICE_TYPE: &str = "E1503";
    pub const CONFLICTING_ADVICE_ORDER: &str = "E1504";
    pub const INVALID_WEAVING_TARGET: &str = "E1505";
    pub const ASPECT_CIRCULAR_DEPENDENCY: &str = "E1506";
    pub const INVALID_POINTCUT_SELECTOR: &str = "E1507";
    pub const ASPECT_NOT_ENABLED: &str = "E1508";

    // Custom block errors (E16xx)
    pub const UNKNOWN_BLOCK_TYPE: &str = "E1601";
    pub const INVALID_BLOCK_SYNTAX: &str = "E1602";
    pub const MATH_BLOCK_INVALID_EXPR: &str = "E1603";
    pub const MATH_BLOCK_UNDEFINED_VAR: &str = "E1604";
    pub const SHELL_BLOCK_INVALID_CMD: &str = "E1605";
    pub const SHELL_BLOCK_UNSAFE_OP: &str = "E1606";
    pub const SQL_BLOCK_SYNTAX_ERROR: &str = "E1607";
    pub const SQL_BLOCK_INVALID_PARAM: &str = "E1608";
    pub const REGEX_BLOCK_INVALID: &str = "E1609";
    pub const REGEX_BLOCK_UNKNOWN_FLAG: &str = "E1610";
    pub const BLOCK_MISSING_CLOSING: &str = "E1611";
    pub const BLOCK_TYPE_MISMATCH: &str = "E1612";

    // Mixin errors (E17xx)
    pub const MIXIN_NOT_FOUND: &str = "E1701";
    pub const MIXIN_METHOD_CONFLICT: &str = "E1702";
    pub const MIXIN_MISSING_REQUIRED: &str = "E1703";
    pub const MIXIN_CIRCULAR_DEPENDENCY: &str = "E1704";
    pub const MIXIN_INVALID_USE: &str = "E1705";
    pub const MIXIN_FIELD_CONFLICT: &str = "E1706";
    pub const MIXIN_SELF_REFERENCE: &str = "E1707";
    pub const MIXIN_TYPE_MISMATCH: &str = "E1708";

    // SDN errors (E18xx)
    pub const SDN_SYNTAX_ERROR: &str = "E1801";
    pub const SDN_UNKNOWN_KEY: &str = "E1802";
    pub const SDN_TYPE_MISMATCH: &str = "E1803";
    pub const SDN_MISSING_REQUIRED: &str = "E1804";
    pub const SDN_DUPLICATE_KEY: &str = "E1805";
    pub const SDN_INVALID_VALUE: &str = "E1806";
    pub const SDN_NESTING_LIMIT: &str = "E1807";
    pub const SDN_CIRCULAR_REFERENCE: &str = "E1808";

    // DI errors (E19xx)
    pub const DI_MISSING_BINDING: &str = "E1901";
    pub const DI_AMBIGUOUS_BINDING: &str = "E1902";
    pub const DI_CIRCULAR_DEPENDENCY: &str = "E1903";
    pub const DI_INVALID_SCOPE: &str = "E1904";
    pub const DI_INJECT_FAILED: &str = "E1905";
    pub const DI_INVALID_ATTRIBUTE: &str = "E1906";
    pub const DI_SCOPE_MISMATCH: &str = "E1907";
    pub const DI_MOCK_NOT_TEST: &str = "E1908";

    // Architecture rule errors (E1Axx)
    pub const ARCH_FORBIDDEN_IMPORT: &str = "E1A01";
    pub const ARCH_FORBIDDEN_DEPEND: &str = "E1A02";
    pub const ARCH_LAYER_VIOLATION: &str = "E1A03";
    pub const ARCH_INVALID_RULE: &str = "E1A04";
    pub const ARCH_CONFLICTING_RULES: &str = "E1A05";
    pub const ARCH_CIRCULAR_MODULES: &str = "E1A06";

    // Codegen errors (E20xx)
    pub const UNSUPPORTED_FEATURE: &str = "E2001";
    pub const FFI_ERROR: &str = "E2002";
    pub const FAILED_BUILD_LOAD: &str = "E2003";
    pub const FAILED_BUILD_STORE: &str = "E2004";
    pub const FAILED_BUILD_ALLOCA: &str = "E2005";
    pub const FAILED_BUILD_CALL: &str = "E2006";
    pub const FAILED_TO_CAST: &str = "E2007";
    pub const FAILED_BUILD_GEP: &str = "E2008";
    pub const UNSUPPORTED_RETURN_TYPE: &str = "E2009";

    // Runtime errors (E30xx)
    pub const DIVISION_BY_ZERO: &str = "E3001";
    pub const INDEX_OUT_OF_BOUNDS: &str = "E3002";
    pub const STACK_OVERFLOW: &str = "E3003";
    pub const ASSERTION_FAILED: &str = "E3004";
    pub const TIMEOUT: &str = "E3005";
    pub const AWAIT_FAILED: &str = "E3006";
    pub const PROMISE_REJECTED: &str = "E3007";
    pub const FUNCTION_NOT_FOUND: &str = "E3008";
    pub const METHOD_NOT_FOUND: &str = "E3009";

    // FFI errors (E40xx)
    pub const TYPE_NOT_FFI_SAFE: &str = "E4005";

    // Contract errors (E50xx)
    pub const CONTRACT_PRECONDITION_FAILED: &str = "E5001";
    pub const CONTRACT_POSTCONDITION_FAILED: &str = "E5002";
    pub const CONTRACT_INVARIANT_FAILED: &str = "E5003";
    pub const CONTRACT_OLD_EXPR_FAILED: &str = "E5004";
}

/// Typo detection and suggestion utilities.
pub mod typo {
    /// Calculate the Levenshtein distance between two strings.
    ///
    /// This measures the minimum number of single-character edits
    /// (insertions, deletions, substitutions) required to change
    /// one string into the other.
    pub fn levenshtein_distance(a: &str, b: &str) -> usize {
        let a_chars: Vec<char> = a.chars().collect();
        let b_chars: Vec<char> = b.chars().collect();
        let a_len = a_chars.len();
        let b_len = b_chars.len();

        if a_len == 0 {
            return b_len;
        }
        if b_len == 0 {
            return a_len;
        }

        // Use two rows instead of full matrix for space efficiency
        let mut prev_row: Vec<usize> = (0..=b_len).collect();
        let mut curr_row: Vec<usize> = vec![0; b_len + 1];

        for (i, a_char) in a_chars.iter().enumerate() {
            curr_row[0] = i + 1;

            for (j, b_char) in b_chars.iter().enumerate() {
                let cost = if a_char == b_char { 0 } else { 1 };
                curr_row[j + 1] = (prev_row[j + 1] + 1) // deletion
                    .min(curr_row[j] + 1) // insertion
                    .min(prev_row[j] + cost); // substitution
            }

            std::mem::swap(&mut prev_row, &mut curr_row);
        }

        prev_row[b_len]
    }

    /// Find similar names from a list of candidates.
    ///
    /// Returns names that are within the given edit distance threshold.
    /// Results are sorted by similarity (closest first).
    pub fn find_similar<'a>(
        name: &str,
        candidates: impl IntoIterator<Item = &'a str>,
        max_distance: usize,
    ) -> Vec<&'a str> {
        let mut matches: Vec<(&str, usize)> = candidates
            .into_iter()
            .filter_map(|candidate| {
                // Skip if lengths differ too much
                let len_diff = (name.len() as isize - candidate.len() as isize).unsigned_abs();
                if len_diff > max_distance {
                    return None;
                }

                let distance = levenshtein_distance(name, candidate);
                if distance <= max_distance && distance > 0 {
                    Some((candidate, distance))
                } else {
                    None
                }
            })
            .collect();

        // Sort by distance (closest first), then alphabetically
        matches.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));

        matches.into_iter().map(|(name, _)| name).collect()
    }

    /// Find the best matching name from a list of candidates.
    ///
    /// Uses dynamic threshold based on name length:
    /// - Short names (≤3 chars): max 1 edit
    /// - Medium names (4-6 chars): max 2 edits
    /// - Long names (>6 chars): max 3 edits
    pub fn suggest_name<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<&'a str> {
        let max_distance = match name.len() {
            0..=3 => 1,
            4..=6 => 2,
            _ => 3,
        };

        find_similar(name, candidates, max_distance).into_iter().next()
    }

    /// Format a suggestion message for a typo.
    ///
    /// Returns `Some("did you mean 'foo'?")` if a suggestion is found,
    /// or `None` if no good match exists.
    pub fn format_suggestion<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<String> {
        suggest_name(name, candidates).map(|suggestion| format!("did you mean '{}'?", suggestion))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_levenshtein_distance() {
            assert_eq!(levenshtein_distance("", ""), 0);
            assert_eq!(levenshtein_distance("abc", "abc"), 0);
            assert_eq!(levenshtein_distance("abc", ""), 3);
            assert_eq!(levenshtein_distance("", "abc"), 3);
            assert_eq!(levenshtein_distance("abc", "abd"), 1);
            assert_eq!(levenshtein_distance("abc", "abcd"), 1);
            assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        }

        #[test]
        fn test_find_similar() {
            let candidates = ["count", "counter", "amount", "account", "mouse"];

            let similar = find_similar("coutn", candidates.iter().copied(), 2);
            assert!(similar.contains(&"count"));

            let similar = find_similar("xyz", candidates.iter().copied(), 2);
            assert!(similar.is_empty());
        }

        #[test]
        fn test_suggest_name() {
            let candidates = ["println", "print", "printf", "sprint"];

            assert_eq!(suggest_name("pritn", candidates.iter().copied()), Some("print"));
            // "printl" has distance 1 to both "print" and "println", alphabetically "print" comes first
            assert_eq!(suggest_name("printl", candidates.iter().copied()), Some("print"));
            assert_eq!(suggest_name("printlnn", candidates.iter().copied()), Some("println"));
            assert_eq!(suggest_name("xyz", candidates.iter().copied()), None);
        }

        #[test]
        fn test_format_suggestion() {
            let candidates = ["foo", "bar", "baz"];

            assert_eq!(
                format_suggestion("fo", candidates.iter().copied()),
                Some("did you mean 'foo'?".to_string())
            );
            assert_eq!(format_suggestion("xyz", candidates.iter().copied()), None);
        }
    }
}

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
    // Codegen Errors
    // ============================================

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

/// Error context for rich diagnostics.
#[derive(Debug, Clone)]
pub struct ErrorContext {
    /// Primary span where the error occurred
    pub span: Option<Span>,
    /// Secondary spans with labels (for related locations)
    pub secondary_spans: Vec<(Span, String)>,
    /// The source file path
    pub file: Option<String>,
    /// The source code (for formatting)
    pub source: Option<String>,
    /// Error code
    pub code: Option<String>,
    /// Additional notes
    pub notes: Vec<String>,
    /// Help suggestions
    pub help: Vec<String>,
}

impl Default for ErrorContext {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorContext {
    /// Create a new empty error context.
    pub fn new() -> Self {
        Self {
            span: None,
            secondary_spans: Vec::new(),
            file: None,
            source: None,
            code: None,
            notes: Vec::new(),
            help: Vec::new(),
        }
    }

    /// Set the primary span.
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Add a secondary span with a label.
    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondary_spans.push((span, label.into()));
        self
    }

    /// Set the file path.
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Set the source code.
    pub fn with_source(mut self, source: impl Into<String>) -> Self {
        self.source = Some(source.into());
        self
    }

    /// Set the error code.
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// Add a note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Add a help suggestion.
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help.push(help.into());
        self
    }
}

/// Compilation errors with optional rich context.
#[derive(Error, Debug)]
pub enum CompileError {
    #[error("io: {0}")]
    Io(String),
    #[error("parse: {0}")]
    Parse(String),
    #[error("semantic: {0}")]
    Semantic(String),
    #[error("codegen: {0}")]
    Codegen(String),
    /// Lint errors (when lint is set to deny level)
    #[error("lint: {0}")]
    Lint(String),
    /// Runtime error during interpretation
    #[error("runtime: {0}")]
    Runtime(String),
    /// Error from ? operator that should be propagated as a return value
    #[error("try: early return")]
    TryError(Value),
    /// Execution was interrupted by user (Ctrl-C)
    #[error("interrupted: execution stopped by user request")]
    InterruptedByUser,
    /// Ghost code verification error (VER-001)
    #[error("ghost: {0}")]
    GhostError(String),

    /// Execution limit exceeded (infinite loop protection)
    #[error("execution limit exceeded: {message}")]
    ExecutionLimitExceeded { limit: u64, message: String },

    /// Stack overflow (recursion depth exceeded)
    #[error("stack overflow: recursion depth {depth} exceeded limit {limit} in function '{function_name}'")]
    StackOverflow { depth: u64, limit: u64, function_name: String },

    /// Execution timeout exceeded (wall-clock)
    #[error("timeout: execution exceeded {timeout_secs} second limit")]
    TimeoutExceeded { timeout_secs: u64 },

    // Rich variants with context (new API)
    #[error("io: {message}")]
    IoWithContext { message: String, context: ErrorContext },
    #[error("parse: {message}")]
    ParseWithContext { message: String, context: ErrorContext },
    #[error("semantic: {message}")]
    SemanticWithContext { message: String, context: ErrorContext },
    #[error("codegen: {message}")]
    CodegenWithContext { message: String, context: ErrorContext },
    #[error("lint: {message}")]
    LintWithContext { message: String, context: ErrorContext },
    #[error("runtime: {message}")]
    RuntimeWithContext { message: String, context: ErrorContext },
}

impl CompileError {
    /// Create an I/O error with just a message.
    pub fn io(message: impl Into<String>) -> Self {
        Self::Io(message.into())
    }

    /// Create a parse error with just a message.
    pub fn parse(message: impl Into<String>) -> Self {
        Self::Parse(message.into())
    }

    /// Create a semantic error with just a message.
    pub fn semantic(message: impl Into<String>) -> Self {
        Self::Semantic(message.into())
    }

    /// Create a codegen error with just a message.
    pub fn codegen(message: impl Into<String>) -> Self {
        Self::Codegen(message.into())
    }

    /// Create a lint error with just a message.
    pub fn lint(message: impl Into<String>) -> Self {
        Self::Lint(message.into())
    }

    /// Create a runtime error with just a message.
    pub fn runtime(message: impl Into<String>) -> Self {
        Self::Runtime(message.into())
    }

    /// Create a contract violation error with a message.
    /// Used when preconditions, postconditions, or invariants fail at runtime.
    pub fn contract_violation(message: impl Into<String>) -> Self {
        let ctx = ErrorContext::new()
            .with_code(codes::CONTRACT_PRECONDITION_FAILED)
            .with_help("ensure the contract condition is satisfied before function call");
        Self::RuntimeWithContext {
            message: message.into(),
            context: ctx,
        }
    }

    /// Create a semantic error with context.
    pub fn semantic_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::SemanticWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a runtime error with context.
    pub fn runtime_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::RuntimeWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a parse error with context.
    pub fn parse_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::ParseWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create an I/O error with context.
    pub fn io_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::IoWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a codegen error with context.
    pub fn codegen_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::CodegenWithContext {
            message: message.into(),
            context,
        }
    }

    /// Get the error context if available.
    pub fn context(&self) -> Option<&ErrorContext> {
        match self {
            Self::IoWithContext { context, .. } => Some(context),
            Self::ParseWithContext { context, .. } => Some(context),
            Self::SemanticWithContext { context, .. } => Some(context),
            Self::CodegenWithContext { context, .. } => Some(context),
            Self::LintWithContext { context, .. } => Some(context),
            Self::RuntimeWithContext { context, .. } => Some(context),
            _ => None,
        }
    }

    /// Get the error message.
    pub fn message(&self) -> &str {
        match self {
            Self::Io(msg) => msg,
            Self::Parse(msg) => msg,
            Self::Semantic(msg) => msg,
            Self::Codegen(msg) => msg,
            Self::Lint(msg) => msg,
            Self::Runtime(msg) => msg,
            Self::IoWithContext { message, .. } => message,
            Self::ParseWithContext { message, .. } => message,
            Self::SemanticWithContext { message, .. } => message,
            Self::CodegenWithContext { message, .. } => message,
            Self::LintWithContext { message, .. } => message,
            Self::RuntimeWithContext { message, .. } => message,
            Self::TryError(_) => "try: early return",
            Self::InterruptedByUser => "interrupted: execution stopped by user request",
            Self::GhostError(msg) => msg,
            Self::ExecutionLimitExceeded { message, .. } => message,
            Self::StackOverflow { function_name, .. } => function_name,
            Self::TimeoutExceeded { .. } => "timeout exceeded",
        }
    }

    /// Get the severity for this error type.
    fn severity(&self) -> Severity {
        match self {
            Self::Lint(_) | Self::LintWithContext { .. } => Severity::Warning,
            _ => Severity::Error,
        }
    }

    /// Convert this error to a rich diagnostic.
    pub fn to_diagnostic(&self) -> Diagnostic {
        let mut diag = if self.severity() == Severity::Warning {
            Diagnostic::warning(self.message())
        } else {
            Diagnostic::error(self.message())
        };

        if let Some(ctx) = self.context() {
            // Set error code
            if let Some(code) = &ctx.code {
                diag = diag.with_code(code.clone());
            }

            // Set file
            if let Some(file) = &ctx.file {
                diag = diag.with_file(file.clone());
            }

            // Add primary label
            if let Some(span) = &ctx.span {
                diag = diag.with_label((*span).into(), self.message());
            }

            // Add secondary labels
            for (span, label) in &ctx.secondary_spans {
                diag = diag.with_secondary_label((*span).into(), label.clone());
            }

            // Add notes
            for note in &ctx.notes {
                diag = diag.with_note(note.clone());
            }

            // Add help
            for help in &ctx.help {
                diag = diag.with_help(help.clone());
            }
        }

        diag
    }

    /// Format this error with source context.
    pub fn format_with_source(&self, source: &str, use_color: bool) -> String {
        self.to_diagnostic().format(source, use_color)
    }
}

// Backward compatibility: allow creating errors from strings
impl From<String> for CompileError {
    fn from(s: String) -> Self {
        Self::semantic(s)
    }
}

impl From<&str> for CompileError {
    fn from(s: &str) -> Self {
        Self::semantic(s)
    }
}

// SPIR-V error conversion (for Vulkan backend)
#[cfg(feature = "vulkan")]
impl From<rspirv::dr::Error> for CompileError {
    fn from(e: rspirv::dr::Error) -> Self {
        Self::Codegen(format!("SPIR-V error: {}", e))
    }
}

// Helper macro for creating errors with context at call site
#[macro_export]
macro_rules! semantic_error {
    ($msg:expr) => {
        $crate::error::CompileError::semantic($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::semantic_with_context($msg, $crate::error::ErrorContext::new().with_span($span))
    };
    ($msg:expr, span = $span:expr, code = $code:expr) => {
        $crate::error::CompileError::semantic_with_context(
            $msg,
            $crate::error::ErrorContext::new().with_span($span).with_code($code),
        )
    };
}

#[macro_export]
macro_rules! runtime_error {
    ($msg:expr) => {
        $crate::error::CompileError::runtime($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::runtime_with_context($msg, $crate::error::ErrorContext::new().with_span($span))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = CompileError::semantic("undefined variable: x");
        assert!(err.message().contains("undefined variable"));
    }

    #[test]
    fn test_error_with_context() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 15, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE)
            .with_help("did you mean 'y'?");

        let err = CompileError::semantic_with_context("undefined variable: x", ctx);
        let diag = err.to_diagnostic();

        assert!(diag.code.as_ref().is_some_and(|c| c == codes::UNDEFINED_VARIABLE));
        assert!(!diag.help.is_empty());
    }

    #[test]
    fn test_diagnostic_format() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 11, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE)
            .with_file("test.spl");

        let err = CompileError::semantic_with_context("undefined variable: x", ctx);
        let source = "fn main():\n    x + 1";
        let formatted = err.format_with_source(source, false);

        assert!(formatted.contains("error"));
        assert!(formatted.contains("E1001"));
        assert!(formatted.contains("test.spl"));
    }

    #[test]
    fn test_backward_compatibility() {
        // Old-style tuple variant creation should still work
        let err = CompileError::Semantic("test error".into());
        assert_eq!(err.message(), "test error");

        // Also test the From trait
        let err2: CompileError = "another error".into();
        assert_eq!(err2.message(), "another error");
    }
}
