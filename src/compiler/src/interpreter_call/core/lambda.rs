// Lambda execution support

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{await_value, evaluate_expr};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef};
use simple_runtime::value::diagram_ffi;
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

pub(crate) fn exec_lambda(
    params: &[String],
    body: &simple_parser::ast::Expr,
    args: &[Argument],
    call_env: &mut Env,
    captured_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::super::block_execution::exec_block_closure;

    // Diagram tracing for lambda execution
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call("<lambda>");
    }

    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        // Automatically await Promise arguments
        let val = await_value(val)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help(format!("lambda expects {} argument(s)", params.len()));
                return Err(CompileError::semantic_with_context(
                    "too many arguments to lambda".to_string(),
                    ctx,
                ));
            }
            local_env.insert(params[positional_idx].clone(), val);
            positional_idx += 1;
        }
    }

    for param in params {
        if !local_env.contains_key(param) {
            local_env.insert(param.clone(), Value::Nil);
        }
    }

    if let Expr::DoBlock(nodes) = body {
        return exec_block_closure(nodes, &mut local_env, functions, classes, enums, impl_methods);
    }

    evaluate_expr(body, &mut local_env, functions, classes, enums, impl_methods)
}
