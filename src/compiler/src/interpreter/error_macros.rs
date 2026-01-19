// Error handling macros to reduce boilerplate

// These macros are defined for potential future use
#[allow(unused_macros)]
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

#[allow(unused_macros)]
/// Create a codegen error with message
macro_rules! codegen_err {
    ($msg:expr) => {
        crate::error::CompileError::Codegen($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Codegen(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)]
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
        let mut msg = format!("unknown method {} on {}", $method, $type_name);
        if let Some(suggestion) = crate::error::typo::format_suggestion($method, $available.iter().copied()) {
            msg.push_str(&format!("; {}", suggestion));
        }
        return Err(semantic_err!("{}", msg));
    }};
}

// Re-export macros for use in parent modules
pub(crate) use runtime_err;
pub(crate) use semantic_err;
pub(crate) use codegen_err;
pub(crate) use bail_runtime;
pub(crate) use bail_semantic;
pub(crate) use bail_unknown_method;
