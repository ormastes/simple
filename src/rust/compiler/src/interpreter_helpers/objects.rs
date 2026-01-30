//! Object creation helpers (Range, Actor)

use crate::error::CompileError;
use crate::value::{Env, Value, BUILTIN_RANGE};
use simple_common::actor::ActorSpawner;
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, RangeBound};
use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex};

use super::super::interpreter_eval::PRELUDE_EXTERN_FUNCTIONS;
use super::super::{
    evaluate_expr, exec_block, exec_function, Control, Enums, ImplMethods, ACTOR_INBOX, ACTOR_OUTBOX, ACTOR_SPAWNER,
    EXTERN_FUNCTIONS,
};

pub(crate) fn create_range_object(start: i64, end: i64, bound: RangeBound) -> Value {
    let mut fields = HashMap::new();
    fields.insert("start".into(), Value::Int(start));
    fields.insert("end".into(), Value::Int(end));
    // Store as boolean for runtime iteration compatibility
    fields.insert("inclusive".into(), Value::Bool(bound.is_inclusive()));
    Value::Object {
        class: BUILTIN_RANGE.into(),
        fields: Arc::new(fields),
    }
}

/// Create a range object with optional start/end values.
/// Missing start defaults to 0 at indexing time.
/// Missing end defaults to collection length at indexing time.
pub(crate) fn create_range_object_opt(start: Option<i64>, end: Option<i64>, bound: RangeBound) -> Value {
    let mut fields = HashMap::new();
    if let Some(s) = start {
        fields.insert("start".into(), Value::Int(s));
    }
    if let Some(e) = end {
        fields.insert("end".into(), Value::Int(e));
    }
    fields.insert("inclusive".into(), Value::Bool(bound.is_inclusive()));
    Value::Object {
        class: BUILTIN_RANGE.into(),
        fields: Arc::new(fields),
    }
}

/// Spawn an actor with the given expression and environment
pub(crate) fn spawn_actor_with_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Value {
    let expr_clone = expr.clone();
    let mut env_clone = env.clone();
    let mut funcs = functions.clone();
    let mut classes_clone = classes.clone();
    let enums_clone = enums.clone();
    let impls_clone = impl_methods.clone();

    let handle = ACTOR_SPAWNER.with(|s| {
        s.spawn(move |inbox, outbox| {
            // Initialize thread-local EXTERN_FUNCTIONS with prelude functions
            EXTERN_FUNCTIONS.with(|cell| {
                let mut externs = cell.borrow_mut();
                externs.clear();
                for &name in PRELUDE_EXTERN_FUNCTIONS {
                    externs.insert(name.to_string());
                }
            });

            let inbox = Arc::new(Mutex::new(inbox));
            ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
            ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));

            // Evaluate the expression to get the function/lambda, then call it
            match evaluate_expr(
                &expr_clone,
                &mut env_clone,
                &mut funcs,
                &mut classes_clone,
                &enums_clone,
                &impls_clone,
            ) {
                Ok(value) => {
                    // If it's a function or lambda, call it with no arguments
                    match value {
                        Value::Function { def, captured_env, .. } => {
                            let mut local_env = captured_env.clone();
                            let _ = exec_block(
                                &def.body,
                                &mut local_env,
                                &mut funcs,
                                &mut classes_clone,
                                &enums_clone,
                                &impls_clone,
                            );
                        }
                        Value::Lambda {
                            body,
                            env: mut lambda_env,
                            ..
                        } => {
                            let _ = evaluate_expr(
                                &body,
                                &mut lambda_env,
                                &mut funcs,
                                &mut classes_clone,
                                &enums_clone,
                                &impls_clone,
                            );
                        }
                        _ => {
                            // Not a callable - just ignore
                        }
                    }
                }
                Err(_) => {
                    // Error evaluating - ignore
                }
            }

            ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
            ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
        })
    });

    // Give the actor thread a moment to start
    std::thread::sleep(std::time::Duration::from_millis(10));

    Value::Actor(handle)
}
