// Public API entry points for module evaluation

use simple_parser::ast::Node;
use tracing::instrument;
use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::error::{codes, CompileError, ErrorContext};
use super::interpreter_state::{set_di_config, set_aop_config};
use super::interpreter_eval;

/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, None, None)
}

pub fn evaluate_module_with_di(items: &[Node], di_config: Option<&DiConfig>) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, di_config, None)
}

pub fn evaluate_module_with_di_and_aop(
    items: &[Node],
    di_config: Option<&DiConfig>,
    aop_config: Option<&AopConfig>,
) -> Result<i32, CompileError> {
    set_di_config(di_config.cloned());
    set_aop_config(aop_config.cloned());
    let result = interpreter_eval::evaluate_module_impl(items);
    set_di_config(None);
    set_aop_config(None);
    result
}

/// Helper to execute a method function with self context (for auto-forwarding properties)
pub(crate) fn exec_method_function(
    method: &simple_parser::ast::FunctionDef,
    args: &[simple_parser::ast::Argument],
    self_val: &crate::value::Value,
    env: &mut crate::value::Env,
    functions: &mut std::collections::HashMap<String, simple_parser::ast::FunctionDef>,
    classes: &mut std::collections::HashMap<String, simple_parser::ast::ClassDef>,
    enums: &super::core_types::Enums,
    impl_methods: &super::core_types::ImplMethods,
) -> Result<crate::value::Value, CompileError> {
    use crate::value::Value;
    use super::interpreter_call::exec_function;

    if let Value::Object { class, fields } = self_val {
        exec_function(
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            Some((class.as_str(), fields)),
        )
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_SELF_TYPE)
            .with_help("method execution requires self to be an object");
        Err(CompileError::semantic_with_context(
            "exec_method_function called with non-object self".to_string(),
            ctx,
        ))
    }
}
