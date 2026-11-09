// Error handling macros to reduce boilerplate

// These macros are defined for potential future use
#[allow(unused_macros)] // reason: macro defined for conditional use; unused in current build configuration
/// Create a runtime error with message
macro_rules! runtime_err {
    ($msg:expr) => {
        crate::error::CompileError::Runtime($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Runtime(format!($fmt, $($arg)*))
    };
}

/// Create a semantic error with message
macro_rules! semantic_err {
    ($msg:expr) => {
        crate::error::CompileError::Semantic($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Semantic(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)] // reason: macro defined for conditional use; unused in current build configuration
/// Create a codegen error with message
macro_rules! codegen_err {
    ($msg:expr) => {
        crate::error::CompileError::Codegen($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Codegen(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)] // reason: macro defined for conditional use; unused in current build configuration
/// Return early with a runtime error
macro_rules! bail_runtime {
    ($msg:expr) => {
        return Err(runtime_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(runtime_err!($fmt, $($arg)*))
    };
}

/// Return early with a semantic error
macro_rules! bail_semantic {
    ($msg:expr) => {
        return Err(semantic_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(semantic_err!($fmt, $($arg)*))
    };
}

/// Return early with unknown method error (with typo suggestions)
macro_rules! bail_unknown_method {
    ($method:expr, $type_name:expr, $available:expr) => {{
        // E1013 - Unknown Method
        let available_vec: Vec<&str> = $available.iter().copied().collect();
        let suggestion = if !available_vec.is_empty() {
            crate::error::typo::suggest_name($method, available_vec.clone())
        } else {
            None
        };

        let mut ctx = crate::error::ErrorContext::new()
            .with_code(crate::error::codes::UNKNOWN_METHOD)
            .with_help("check the method name and type definition");

        if let Some(best_match) = suggestion {
            ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
        }

        if !available_vec.is_empty() && available_vec.len() <= 5 {
            let methods_list = available_vec.join(", ");
            ctx = ctx.with_note(format!("available methods: {}", methods_list));
        }

        // Location probe (bug phase2_stage2_native_build_len_on_i64_aarch64_linux_2026-09-13):
        // the bare "method `len` not found on type `i64`" carried no file and no
        // enclosing function, so a failure inside a ~1800-module native-build
        // worker graph could not be located. Interpreter exprs carry no spans, so
        // attach the module being evaluated (always; error path only) and, under
        // SIMPLE_BOOTSTRAP_DIAG / SIMPLE_DEBUG_FIELD_ACCESS (which populate
        // DEBUG_CALL_STACK), the innermost interpreted functions.
        if let Some(file) = crate::interpreter::get_current_file() {
            let file = file.display().to_string();
            ctx = ctx.with_note(format!("while evaluating module: {}", file)).with_file(file);
        }
        if crate::interpreter::field_access_debug_enabled() {
            let stack = crate::interpreter::debug_call_stack_snapshot();
            let tail: Vec<&str> = stack.iter().rev().take(12).map(|s| s.as_str()).collect();
            ctx = ctx.with_note(format!("interpreted call stack (innermost first): {:?}", tail));
            eprintln!(
                "[unknown-method] method={} type={} call_stack_top={:?}",
                $method, $type_name, tail
            );
        }

        return Err(crate::error::CompileError::semantic_with_context(
            format!("method `{}` not found on type `{}`", $method, $type_name),
            ctx,
        ));
    }};
}

// Re-export macros for use in parent modules
pub(crate) use runtime_err;
pub(crate) use semantic_err;
pub(crate) use codegen_err;
pub(crate) use bail_runtime;
pub(crate) use bail_semantic;
pub(crate) use bail_unknown_method;
