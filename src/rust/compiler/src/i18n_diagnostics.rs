//! Conversion utilities for compiler errors to i18n diagnostics.
//!
//! This module provides functions to convert `CompileError` instances
//! to localized `simple-diagnostics::Diagnostic` instances with proper
//! i18n message loading.

use crate::error::{codes, CompileError, ErrorContext};
use simple_diagnostics::{
    Diagnostic as I18nDiagnostic, Severity as I18nSeverity, Span as I18nSpan,
    i18n::{ctx1, ctx2, ctx3, ContextBuilder},
};
use simple_i18n::MessageContext;

/// Convert a compiler error to an i18n diagnostic.
///
/// This function examines the error context and error code to determine
/// which localized message to use from the compiler catalog.
pub fn convert_compiler_error(error: &CompileError) -> I18nDiagnostic {
    // Get the context if available
    if let Some(ctx) = error.context() {
        // Convert span
        let span = ctx.span.map(|s| I18nSpan::new(s.start, s.end, s.line, s.column));

        // Determine error code and create i18n diagnostic
        if let Some(code) = &ctx.code {
            let i18n_diag = create_i18n_diagnostic_from_code(code, error.message(), ctx);

            // Add span if available
            let mut diag = if let Some(s) = span {
                i18n_diag.with_span(s)
            } else {
                i18n_diag
            };

            // Add secondary labels
            for (sec_span, label) in &ctx.secondary_spans {
                let sec_i18n_span = I18nSpan::new(sec_span.start, sec_span.end, sec_span.line, sec_span.column);
                diag = diag.with_label(sec_i18n_span, label.clone());
            }

            // Add notes
            for note in &ctx.notes {
                diag = diag.with_note(note.clone());
            }

            // Add help
            for help in &ctx.help {
                diag = diag.with_help(help.clone());
            }

            diag
        } else {
            // No error code, create a plain diagnostic
            create_plain_diagnostic(error, span)
        }
    } else {
        // No context, create a simple diagnostic with just the message
        create_plain_diagnostic(error, None)
    }
}

/// Create an i18n diagnostic from an error code.
fn create_i18n_diagnostic_from_code(code: &str, message: &str, ctx: &ErrorContext) -> I18nDiagnostic {
    match code {
        // Semantic errors (E10xx)
        codes::UNDEFINED_VARIABLE => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1001", &msg_ctx)
        }

        codes::UNDEFINED_FUNCTION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1002", &msg_ctx)
        }

        codes::TYPE_MISMATCH => {
            let (expected, found) = extract_type_mismatch(message);
            let msg_ctx = ctx2("expected", expected, "found", found);
            I18nDiagnostic::error_i18n("compiler", "E1003", &msg_ctx)
        }

        codes::INVALID_ASSIGNMENT => {
            let target = extract_target_from_message(message);
            let msg_ctx = ctx1("target", target);
            I18nDiagnostic::error_i18n("compiler", "E1004", &msg_ctx)
        }

        codes::INVALID_OPERATION => {
            let (operator, type_name) = extract_operation_info(message);
            let msg_ctx = ctx2("operator", operator, "type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1005", &msg_ctx)
        }

        codes::INVALID_PATTERN => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1006", &msg_ctx)
        }

        codes::MISSING_FIELD => {
            let (struct_name, field_name) = extract_field_info(message);
            let msg_ctx = ctx2("struct_name", struct_name, "field_name", field_name);
            I18nDiagnostic::error_i18n("compiler", "E1007", &msg_ctx)
        }

        codes::DUPLICATE_DEFINITION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1008", &msg_ctx)
        }

        codes::CIRCULAR_DEPENDENCY => {
            let msg_ctx = ctx1("cycle", message);
            I18nDiagnostic::error_i18n("compiler", "E1009", &msg_ctx)
        }

        codes::MODULE_NOT_FOUND => {
            let module = extract_module_name(message);
            let msg_ctx = ctx1("module", module);
            I18nDiagnostic::error_i18n("compiler", "E1010", &msg_ctx)
        }

        // Control flow errors (E11xx)
        codes::BREAK_OUTSIDE_LOOP => I18nDiagnostic::error_i18n("compiler", "E1101", &MessageContext::new()),

        codes::CONTINUE_OUTSIDE_LOOP => I18nDiagnostic::error_i18n("compiler", "E1102", &MessageContext::new()),

        codes::RETURN_OUTSIDE_FUNCTION => I18nDiagnostic::error_i18n("compiler", "E1103", &MessageContext::new()),

        // Macro errors (E14xx)
        codes::MACRO_UNDEFINED => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1401", &msg_ctx)
        }

        codes::MACRO_USED_BEFORE_DEFINITION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1402", &msg_ctx)
        }

        // Codegen errors (E20xx)
        codes::UNSUPPORTED_FEATURE => {
            let feature = extract_feature_name(message);
            let msg_ctx = ctx1("feature", feature);
            I18nDiagnostic::error_i18n("compiler", "E2001", &msg_ctx)
        }

        codes::FFI_ERROR => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E2002", &msg_ctx)
        }

        // Runtime errors (E30xx)
        codes::DIVISION_BY_ZERO => I18nDiagnostic::error_i18n("compiler", "E3001", &MessageContext::new()),

        codes::INDEX_OUT_OF_BOUNDS => {
            let (index, length) = extract_index_bounds(message);
            let msg_ctx = ctx2("index", index, "length", length);
            I18nDiagnostic::error_i18n("compiler", "E3002", &msg_ctx)
        }

        codes::STACK_OVERFLOW => I18nDiagnostic::error_i18n("compiler", "E3003", &MessageContext::new()),

        codes::ASSERTION_FAILED => {
            let condition = extract_condition(message);
            let note_msg = ctx.notes.first().map(|s| s.as_str()).unwrap_or("");
            let msg_ctx = ctx2("condition", condition, "message", note_msg);
            I18nDiagnostic::error_i18n("compiler", "E3004", &msg_ctx)
        }

        codes::TIMEOUT => {
            let duration = extract_duration(message);
            let msg_ctx = ctx1("duration", duration);
            I18nDiagnostic::error_i18n("compiler", "E3005", &msg_ctx)
        }

        codes::AWAIT_FAILED => {
            let msg_ctx = ctx1("error", message);
            I18nDiagnostic::error_i18n("compiler", "E3006", &msg_ctx)
        }

        codes::PROMISE_REJECTED => {
            let msg_ctx = ctx1("reason", message);
            I18nDiagnostic::error_i18n("compiler", "E3007", &msg_ctx)
        }

        codes::FUNCTION_NOT_FOUND => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E3008", &msg_ctx)
        }

        codes::METHOD_NOT_FOUND => {
            let (method, type_name) = extract_method_info(message);
            let msg_ctx = ctx2("method", method, "type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E3009", &msg_ctx)
        }

        // Extended semantic errors (E1011-E1080)
        codes::UNDEFINED_TYPE => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1011", &msg_ctx)
        }

        codes::UNDEFINED_FIELD => {
            let field = extract_name_from_message(message);
            let msg_ctx = ctx1("field", field);
            I18nDiagnostic::error_i18n("compiler", "E1012", &msg_ctx)
        }

        codes::UNKNOWN_METHOD => {
            let (method, type_name) = extract_method_info(message);
            let msg_ctx = ctx2("method", method, "type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1013", &msg_ctx)
        }

        codes::UNKNOWN_CLASS => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1014", &msg_ctx)
        }

        codes::UNKNOWN_ENUM => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1015", &msg_ctx)
        }

        codes::LET_BINDING_FAILED => {
            let msg_ctx = ctx2("name", extract_name_from_message(message), "error", message);
            I18nDiagnostic::error_i18n("compiler", "E1016", &msg_ctx)
        }

        codes::IMPURE_FUNCTION_IN_CONTRACT => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1017", &msg_ctx)
        }

        codes::EFFECT_DECLARATION_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1018", &msg_ctx)
        }

        codes::DUPLICATE_BINDING => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1019", &msg_ctx)
        }

        codes::ARGUMENT_COUNT_MISMATCH => {
            let (expected, found) = extract_count_mismatch(message);
            let msg_ctx = ctx2("expected", expected, "found", found);
            I18nDiagnostic::error_i18n("compiler", "E1020", &msg_ctx)
        }

        codes::MISSING_STRUCT_FIELDS => {
            let msg_ctx = ctx1("fields", message);
            I18nDiagnostic::error_i18n("compiler", "E1021", &msg_ctx)
        }

        codes::INVALID_LHS_ASSIGNMENT => {
            let msg_ctx = ctx1("lhs", message);
            I18nDiagnostic::error_i18n("compiler", "E1022", &msg_ctx)
        }

        codes::INVALID_STRUCT_LITERAL => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1023", &msg_ctx)
        }

        codes::CONST_EVAL_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1024", &msg_ctx)
        }

        codes::DUPLICATE_METHOD => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1025", &msg_ctx)
        }

        codes::UNKNOWN_ASSOC_TYPE => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1026", &msg_ctx)
        }

        codes::UNCONSTRAINED_TYPE_PARAM => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1027", &msg_ctx)
        }

        codes::UNKNOWN_ASSOC_TYPE_NAME => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1028", &msg_ctx)
        }

        codes::CONFLICTING_TRAIT_BOUNDS => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1029", &msg_ctx)
        }

        codes::INVALID_LIFETIME_ON_TRAIT => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1030", &msg_ctx)
        }

        codes::MISSING_TRAIT_METHOD => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1031", &msg_ctx)
        }

        codes::SELF_IN_STATIC => I18nDiagnostic::error_i18n("compiler", "E1032", &MessageContext::new()),

        codes::INVALID_SELF_IMPORT => I18nDiagnostic::error_i18n("compiler", "E1033", &MessageContext::new()),

        codes::UNRESOLVED_IMPORT => {
            let msg_ctx = ctx1("path", message);
            I18nDiagnostic::error_i18n("compiler", "E1034", &msg_ctx)
        }

        codes::INVALID_SELF_CONTEXT => I18nDiagnostic::error_i18n("compiler", "E1035", &MessageContext::new()),

        codes::CLOSURE_CAPTURE_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1036", &msg_ctx)
        }

        codes::INVALID_SELF_PARAM => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1037", &msg_ctx)
        }

        codes::PRIVATE_IN_PUBLIC => {
            let msg_ctx = ctx1("item", message);
            I18nDiagnostic::error_i18n("compiler", "E1038", &msg_ctx)
        }

        codes::INVALID_VISIBILITY => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1039", &msg_ctx)
        }

        codes::PRIVATE_FIELD_ACCESS => {
            let field = extract_name_from_message(message);
            let msg_ctx = ctx1("field", field);
            I18nDiagnostic::error_i18n("compiler", "E1040", &msg_ctx)
        }

        codes::INVALID_UNARY_OP => {
            let (operator, type_name) = extract_operation_info(message);
            let msg_ctx = ctx2("operator", operator, "type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1041", &msg_ctx)
        }

        codes::INVALID_SELF_TYPE => I18nDiagnostic::error_i18n("compiler", "E1042", &MessageContext::new()),

        codes::INVALID_INDEX_TYPE => {
            let msg_ctx = ctx1("found", message);
            I18nDiagnostic::error_i18n("compiler", "E1043", &msg_ctx)
        }

        codes::TUPLE_INDEX_OOB => {
            let (index, size) = extract_index_bounds(message);
            let msg_ctx = ctx2("index", index, "size", size);
            I18nDiagnostic::error_i18n("compiler", "E1044", &msg_ctx)
        }

        codes::INVALID_FIELD_ASSIGN => I18nDiagnostic::error_i18n("compiler", "E1045", &MessageContext::new()),

        codes::PRIVATE_FIELD => {
            let field = extract_name_from_message(message);
            let msg_ctx = ctx1("field", field);
            I18nDiagnostic::error_i18n("compiler", "E1046", &msg_ctx)
        }

        codes::CANNOT_BORROW_MUT_FIELD => {
            let field = extract_name_from_message(message);
            let msg_ctx = ctx1("field", field);
            I18nDiagnostic::error_i18n("compiler", "E1047", &msg_ctx)
        }

        codes::NOT_CALLABLE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1048", &msg_ctx)
        }

        codes::CANNOT_CALL_NON_FUNCTION => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1049", &msg_ctx)
        }

        codes::DISALLOWED_COERCION => {
            let (from, to) = extract_type_mismatch(message);
            let msg_ctx = ctx2("from", from, "to", to);
            I18nDiagnostic::error_i18n("compiler", "E1050", &msg_ctx)
        }

        codes::CLOSURE_SIGNATURE_MISMATCH => I18nDiagnostic::error_i18n("compiler", "E1051", &MessageContext::new()),

        codes::INVALID_LET_ELSE_PATTERN => I18nDiagnostic::error_i18n("compiler", "E1052", &MessageContext::new()),

        codes::CANNOT_BORROW_IMMUTABLE => I18nDiagnostic::error_i18n("compiler", "E1053", &MessageContext::new()),

        codes::INVALID_DEREFERENCE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1054", &msg_ctx)
        }

        codes::TYPE_ALIAS_BOUNDS => I18nDiagnostic::error_i18n("compiler", "E1055", &MessageContext::new()),

        codes::INVALID_RANGE => I18nDiagnostic::error_i18n("compiler", "E1056", &MessageContext::new()),

        codes::YIELD_OUTSIDE_GENERATOR => I18nDiagnostic::error_i18n("compiler", "E1057", &MessageContext::new()),

        codes::INVALID_DOC_COMMENT => I18nDiagnostic::error_i18n("compiler", "E1058", &MessageContext::new()),

        codes::INVALID_IMPLICIT_DEREFERENCE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1059", &msg_ctx)
        }

        codes::INVALID_CONST_EXPRESSION => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1060", &msg_ctx)
        }

        codes::EMPTY_ENUM => I18nDiagnostic::error_i18n("compiler", "E1061", &MessageContext::new()),

        codes::RECURSION_LIMIT_EXCEEDED => I18nDiagnostic::error_i18n("compiler", "E1062", &MessageContext::new()),

        codes::TYPE_SIZE_LIMIT_EXCEEDED => I18nDiagnostic::error_i18n("compiler", "E1063", &MessageContext::new()),

        codes::WRONG_INTRINSIC_TYPE => {
            let msg_ctx = ctx3(
                "intrinsic",
                extract_name_from_message(message),
                "expected",
                "?",
                "found",
                "?",
            );
            I18nDiagnostic::error_i18n("compiler", "E1064", &msg_ctx)
        }

        codes::INVALID_RETURN_TYPE => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1065", &msg_ctx)
        }

        codes::INVALID_MAIN_SIGNATURE => I18nDiagnostic::error_i18n("compiler", "E1066", &MessageContext::new()),

        codes::INVALID_BUILTIN_ATTRIBUTE => {
            let attr = extract_name_from_message(message);
            let msg_ctx = ctx1("attr", attr);
            I18nDiagnostic::error_i18n("compiler", "E1067", &msg_ctx)
        }

        codes::INCONSISTENT_BINDINGS => I18nDiagnostic::error_i18n("compiler", "E1068", &MessageContext::new()),

        codes::MISMATCHED_BINDING => I18nDiagnostic::error_i18n("compiler", "E1069", &MessageContext::new()),

        codes::INVALID_DEFAULT_VARIANT => I18nDiagnostic::error_i18n("compiler", "E1070", &MessageContext::new()),

        codes::INVALID_ATTRIBUTE_POSITION => {
            let attr = extract_name_from_message(message);
            let msg_ctx = ctx1("attr", attr);
            I18nDiagnostic::error_i18n("compiler", "E1071", &msg_ctx)
        }

        codes::INVALID_DESTRUCTURING => I18nDiagnostic::error_i18n("compiler", "E1072", &MessageContext::new()),

        codes::NON_EXHAUSTIVE_TYPE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1073", &msg_ctx)
        }

        codes::CONFLICTING_REPRESENTATION => I18nDiagnostic::error_i18n("compiler", "E1074", &MessageContext::new()),

        codes::DISCRIMINANT_OVERFLOW => I18nDiagnostic::error_i18n("compiler", "E1075", &MessageContext::new()),

        codes::UNKNOWN_INTRINSIC => {
            let intrinsic = extract_name_from_message(message);
            let msg_ctx = ctx1("intrinsic", intrinsic);
            I18nDiagnostic::error_i18n("compiler", "E1076", &msg_ctx)
        }

        codes::WRONG_INTRINSIC_SIGNATURE => {
            let intrinsic = extract_name_from_message(message);
            let msg_ctx = ctx1("intrinsic", intrinsic);
            I18nDiagnostic::error_i18n("compiler", "E1077", &msg_ctx)
        }

        codes::INVALID_INTRINSIC_RETURN => {
            let intrinsic = extract_name_from_message(message);
            let msg_ctx = ctx1("intrinsic", intrinsic);
            I18nDiagnostic::error_i18n("compiler", "E1078", &msg_ctx)
        }

        codes::MISSING_GENERIC_ARGUMENTS => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1079", &msg_ctx)
        }

        codes::TYPE_TOO_COMPLEX => I18nDiagnostic::error_i18n("compiler", "E1080", &MessageContext::new()),

        // Extended control flow errors
        codes::RETURN_IN_CLOSURE => I18nDiagnostic::error_i18n("compiler", "E1104", &MessageContext::new()),

        codes::INVALID_CONTROL_FLOW => I18nDiagnostic::error_i18n("compiler", "E1105", &MessageContext::new()),

        // Capability errors (E13xx)
        codes::CAPABILITY_VIOLATION => I18nDiagnostic::error_i18n("compiler", "E1301", &MessageContext::new()),

        codes::ISOLATION_VIOLATION => I18nDiagnostic::error_i18n("compiler", "E1302", &MessageContext::new()),

        // Extended macro errors
        codes::KEYWORD_IN_MACRO => {
            let keyword = extract_name_from_message(message);
            let msg_ctx = ctx1("keyword", keyword);
            I18nDiagnostic::error_i18n("compiler", "E1403", &msg_ctx)
        }

        // Extended codegen errors
        codes::FAILED_BUILD_LOAD => I18nDiagnostic::error_i18n("compiler", "E2003", &MessageContext::new()),

        codes::FAILED_BUILD_STORE => I18nDiagnostic::error_i18n("compiler", "E2004", &MessageContext::new()),

        codes::FAILED_BUILD_ALLOCA => I18nDiagnostic::error_i18n("compiler", "E2005", &MessageContext::new()),

        codes::FAILED_BUILD_CALL => I18nDiagnostic::error_i18n("compiler", "E2006", &MessageContext::new()),

        codes::FAILED_TO_CAST => {
            let (from_type, to_type) = extract_type_mismatch(message);
            let msg_ctx = ctx2("from_type", from_type, "to_type", to_type);
            I18nDiagnostic::error_i18n("compiler", "E2007", &msg_ctx)
        }

        codes::FAILED_BUILD_GEP => I18nDiagnostic::error_i18n("compiler", "E2008", &MessageContext::new()),

        codes::UNSUPPORTED_RETURN_TYPE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E2009", &msg_ctx)
        }

        // Context errors (E10xx continued)
        codes::INVALID_CONTEXT => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1081", &msg_ctx)
        }

        // Actor/Concurrency errors (E12xx)
        codes::ACTOR_SEND_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1201", &msg_ctx)
        }

        codes::ACTOR_RECV_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1202", &msg_ctx)
        }

        codes::CHANNEL_CLOSED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1203", &msg_ctx)
        }

        codes::DEADLOCK_DETECTED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1204", &msg_ctx)
        }

        codes::ACTOR_JOIN_FAILED => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1205", &msg_ctx)
        }

        // Custom block errors (E16xx)
        codes::UNKNOWN_BLOCK_TYPE => {
            let kind = extract_name_from_message(message);
            let msg_ctx = ctx1("kind", kind);
            I18nDiagnostic::error_i18n("compiler", "E1601", &msg_ctx)
        }

        // FFI errors (E40xx)
        codes::TYPE_NOT_FFI_SAFE => {
            let type_name = extract_type_from_message(message);
            let msg_ctx = ctx1("type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E4005", &msg_ctx)
        }

        // Unknown error code - fall back to plain diagnostic
        _ => create_plain_diagnostic_with_code(message, code, None),
    }
}

/// Create a plain diagnostic without i18n (fallback).
fn create_plain_diagnostic(error: &CompileError, span: Option<I18nSpan>) -> I18nDiagnostic {
    let severity = match error {
        CompileError::Lint(_) | CompileError::LintWithContext { .. } => I18nSeverity::Warning,
        _ => I18nSeverity::Error,
    };

    let mut diag = I18nDiagnostic::new(severity, error.message().to_string());

    if let Some(s) = span {
        diag = diag.with_span(s);
    }

    diag
}

/// Create a plain diagnostic with an error code.
fn create_plain_diagnostic_with_code(message: &str, code: &str, span: Option<I18nSpan>) -> I18nDiagnostic {
    let mut diag = I18nDiagnostic::error(message.to_string()).with_code(code.to_string());

    if let Some(s) = span {
        diag = diag.with_span(s);
    }

    diag
}

// Helper functions to extract context from error messages

fn extract_name_from_message(message: &str) -> &str {
    // Extract name from messages like "undefined variable: foo" or "cannot find variable `foo` in this scope"
    if let Some(pos) = message.find('`') {
        if let Some(end_pos) = message[pos + 1..].find('`') {
            return &message[pos + 1..pos + 1 + end_pos];
        }
    }

    if let Some(pos) = message.find(": ") {
        message[pos + 2..].trim()
    } else {
        "unknown"
    }
}

fn extract_type_from_message(message: &str) -> &str {
    // Extract type name from messages like "type `Foo` is not FFI-safe" or "missing generic arguments for `Bar<T>`"
    if let Some(pos) = message.find("type `") {
        let start = pos + "type `".len();
        if let Some(end) = message[start..].find('`') {
            return &message[start..start + end];
        }
    }

    // Fall back to general backtick extraction
    if let Some(pos) = message.find('`') {
        if let Some(end_pos) = message[pos + 1..].find('`') {
            return &message[pos + 1..pos + 1 + end_pos];
        }
    }

    "unknown"
}

fn extract_type_mismatch(message: &str) -> (&str, &str) {
    // Extract from "expected type `Foo`, found `Bar`"
    let expected = if let Some(start) = message.find("expected type `") {
        let start_pos = start + "expected type `".len();
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    let found = if let Some(start) = message.find("found `") {
        let start_pos = start + "found `".len();
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    (expected, found)
}

/// Helper to extract a number following a keyword in a message
fn extract_number_after_keyword<'a>(message: &'a str, keyword: &str) -> &'a str {
    if let Some(start) = message.find(keyword) {
        let start_pos = start + keyword.len();
        // Find the next space or non-digit character
        let mut end = start_pos;
        for (i, c) in message[start_pos..].char_indices() {
            if !c.is_ascii_digit() {
                end = start_pos + i;
                break;
            }
            end = start_pos + i + 1;
        }
        if end > start_pos {
            &message[start_pos..end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    }
}

/// Helper to extract a backtick-quoted string following a keyword in a message
/// E.g., extract_quoted("struct `Foo` ...", "struct `") returns "Foo"
fn extract_quoted<'a>(message: &'a str, keyword: &str) -> &'a str {
    if let Some(start) = message.find(keyword) {
        let start_pos = start + keyword.len();
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    }
}

fn extract_count_mismatch(message: &str) -> (&str, &str) {
    // Extract from "expected 3 arguments, found 2" or similar patterns
    let expected = extract_number_after_keyword(message, "expected ");
    let found = extract_number_after_keyword(message, "found ");
    (expected, found)
}

fn extract_target_from_message(message: &str) -> &str {
    // Extract from "cannot assign to `foo`"
    if let Some(pos) = message.find("to `") {
        let start_pos = pos + 4;
        if let Some(end) = message[start_pos..].find('`') {
            return &message[start_pos..start_pos + end];
        }
    }
    "expression"
}

fn extract_operation_info(message: &str) -> (&str, &str) {
    // Extract from "cannot apply operator `+` to type `String`"
    let operator = extract_quoted(message, "operator `");
    let type_name = extract_quoted(message, "type `");
    (operator, type_name)
}

fn extract_field_info(message: &str) -> (&str, &str) {
    // Extract from "struct `Foo` does not have a field named `bar`"
    let struct_name = extract_quoted(message, "struct `");
    let field_name = extract_quoted(message, "field named `");
    (struct_name, field_name)
}

fn extract_module_name(message: &str) -> &str {
    // Extract from "module `foo` not found"
    extract_quoted(message, "module `")
}

fn extract_feature_name(message: &str) -> &str {
    // Extract from "feature `foo` is not supported in this context"
    extract_quoted(message, "feature `")
}

fn extract_index_bounds(message: &str) -> (&str, &str) {
    // Extract from "index 5 out of bounds for array of length 3"
    let index = if let Some(start) = message.find("index ") {
        let start_pos = start + 6;
        if let Some(end) = message[start_pos..].find(' ') {
            &message[start_pos..start_pos + end]
        } else {
            "0"
        }
    } else {
        "0"
    };

    let length = if let Some(start) = message.find("length ") {
        let start_pos = start + 7;
        message[start_pos..].split_whitespace().next().unwrap_or("0")
    } else {
        "0"
    };

    (index, length)
}

fn extract_condition(message: &str) -> &str {
    // Extract from "assertion failed: condition"
    if let Some(pos) = message.find("failed: ") {
        &message[pos + 8..]
    } else {
        "assertion"
    }
}

fn extract_duration(message: &str) -> &str {
    // Extract from "operation timed out after 5s"
    if let Some(pos) = message.find("after ") {
        &message[pos + 6..]
    } else {
        "timeout"
    }
}

fn extract_method_info(message: &str) -> (&str, &str) {
    // Extract from "method `foo` not found on type `Bar`" or similar
    let method = if message.contains("`method") {
        extract_quoted(message, "`method")
    } else {
        extract_quoted(message, "`")
    };

    let type_name = extract_quoted(message, "type `");

    (method, type_name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Span;

    #[test]
    fn test_convert_undefined_variable() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 11, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE);

        let err = CompileError::semantic_with_context("cannot find variable `x` in this scope", ctx);
        let diag = convert_compiler_error(&err);

        assert_eq!(diag.code.as_ref().unwrap(), "E1001");
    }

    #[test]
    fn test_convert_type_mismatch() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 15, 2, 5))
            .with_code(codes::TYPE_MISMATCH);

        let err = CompileError::semantic_with_context("expected type `Int`, found `String`", ctx);
        let diag = convert_compiler_error(&err);

        assert_eq!(diag.code.as_ref().unwrap(), "E1003");
    }

    #[test]
    fn test_extract_name_from_message() {
        assert_eq!(
            extract_name_from_message("cannot find variable `foo` in this scope"),
            "foo"
        );
        assert_eq!(extract_name_from_message("undefined variable: bar"), "bar");
    }

    #[test]
    fn test_extract_type_mismatch() {
        let (expected, found) = extract_type_mismatch("expected type `Int`, found `String`");
        assert_eq!(expected, "Int");
        assert_eq!(found, "String");
    }

    #[test]
    fn test_extract_index_bounds() {
        let (index, length) = extract_index_bounds("index 5 out of bounds for array of length 3");
        assert_eq!(index, "5");
        assert_eq!(length, "3");
    }
}
