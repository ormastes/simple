use std::sync::Arc;
use std::collections::HashMap;

use tracing::instrument;

use simple_parser::ast::Expr;

use crate::effects::check_effect_violations;
use crate::error::{codes, ErrorContext};
use crate::value::{enum_names, OptionVariant, ResultVariant, SpecialEnumType};

use super::{
    evaluate_macro_invocation, spawn_actor_with_expr, take_macro_introduced_symbols, ClassDef, CompileError, Enums,
    Env, FunctionDef, ImplMethods, Value, GENERATOR_YIELDS, evaluate_method_call, exec_lambda,
    exec_function_with_captured_env,
};

/// Helper to unwrap Option or Result values, returning Some(inner_value) or None
pub(super) fn try_unwrap_option_or_result(val: &Value) -> Option<Value> {
    match val {
        Value::Enum {
            ref enum_name,
            ref variant,
            ref payload,
        } => {
            if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) {
                if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
                    payload.as_ref().map(|p| p.as_ref().clone())
                } else {
                    None
                }
            } else if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) {
                if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
                    payload.as_ref().map(|p| p.as_ref().clone())
                } else {
                    None
                }
            } else {
                // A USER enum (`Color.Green`) is not an Option/Result, so
                // there is nothing to unwrap: `!` is the identity on the
                // value and only narrows the static type `Color?` -> `Color`.
                // Returning None here made the interpreter raise
                // `force unwrap failed: expected Some or Ok, got Color::Green`
                // while the JIT accepted it — an engine divergence.
                // Mirrors the JIT's `lower_try` non-enum-nullable identity
                // guard (hir/lower/expr/control.rs, `Some(HirType::Struct{..})
                // | Some(HirType::Enum{..})`).
                // Bug: doc/08_tracking/bug/jit_optional_class_unwrap_field_access_segv_2026-08-20.md
                Some(val.clone())
            }
        }
        // Nil is treated as "absent" (like None/Err)
        Value::Nil => None,
        // Any other non-Option/non-Result value is treated as "present"
        other => Some(other.clone()),
    }
}

/// Helper to call a closure/lambda value with no arguments
fn call_closure_no_args(
    closure: Value,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match closure {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut captured_clone = Env::clone(&captured);
            exec_lambda(
                &params, // params is already Vec<String>
                &body,
                &[],
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::Function { def, captured_env, .. } => {
            let mut captured_env_clone = Env::clone(&captured_env);
            exec_function_with_captured_env(
                &def,
                &[],
                env,
                &mut captured_env_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("expected a closure or function");
            Err(CompileError::semantic_with_context(
                format!("expected callable, got {}", closure.type_name()),
                ctx,
            ))
        }
    }
}

/// Bind the present `?.` payload to a scratch local for the duration of
/// `body`, restoring any outer binding of the same name afterwards (nested
/// chains reuse the name).
fn with_optional_chain_temp(
    env: &mut Env,
    payload: Value,
    body: impl FnOnce(&mut Env, Box<Expr>) -> Result<Value, CompileError>,
) -> Result<Value, CompileError> {
    let name = "__optional_chain_temp__".to_string();
    let saved = env.insert(name.clone(), payload);
    let result = body(env, Box::new(Expr::Identifier(name.clone())));
    match saved {
        Some(prev) => {
            env.insert(name, prev);
        }
        None => {
            env.remove(&name);
        }
    }
    result
}

mod calls;
pub(crate) use calls::{receiver_root_identifier, refresh_stale_module_global_receiver};
mod collections;
mod control;
mod literals;
mod ops;

mod casting;
mod units;

/// Route an expression to the correct sub-evaluator in O(1) — one discriminant check.
///
/// The original design called all 5 sub-evaluators in sequence; each did a full `match expr`
/// internally and returned `None` if the variant wasn't theirs. For common variants (Call,
/// MethodCall, Binary) that meant 1–4 wasted enum-match traversals per expression node.
///
/// This router maps each `Expr` variant to exactly the sub-evaluator that owns it, then
/// falls through to the residual `match` in `evaluate_expr` for variants that live there.
/// Variants not listed here are handled by the match below.
#[inline(always)]
fn route_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Option<Result<Value, CompileError>> {
    match expr {
        // --- literals ---
        Expr::Integer(_)
        | Expr::TypedInteger(_, _)
        | Expr::Float(_)
        | Expr::TypedFloat(_, _)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::String(_)
        | Expr::TypedString(_, _)
        | Expr::FString { .. }
        | Expr::Symbol(_)
        | Expr::I18nString { .. }
        | Expr::I18nTemplate { .. }
        | Expr::I18nRef(_)
        | Expr::BlockExpr { .. }
        | Expr::Identifier(_) => {
            literals::eval_literal_expr(expr, env, functions, classes, enums, impl_methods).transpose()
        }
        // --- ops ---
        Expr::Binary { .. } | Expr::Unary { .. } | Expr::New { .. } | Expr::Cast { .. } => {
            ops::eval_op_expr(expr, env, functions, classes, enums, impl_methods).transpose()
        }
        // --- control flow ---
        Expr::Lambda { .. } | Expr::If { .. } | Expr::Match { .. } | Expr::DoBlock(_) | Expr::UnsafeBlock(_, _) => {
            control::eval_control_expr(expr, env, functions, classes, enums, impl_methods).transpose()
        }
        // --- calls & field access ---
        Expr::Call { .. }
        | Expr::MethodCall { .. }
        | Expr::FieldAccess { .. }
        | Expr::FunctionalUpdate { .. }
        | Expr::KernelLaunch { .. } => {
            calls::eval_call_expr(expr, env, functions, classes, enums, impl_methods).transpose()
        }
        // --- collections & indexing ---
        Expr::Array(_)
        | Expr::VecLiteral(_)
        | Expr::ArrayRepeat { .. }
        | Expr::Tuple(_)
        | Expr::LabeledTuple(_)
        | Expr::Dict(_)
        | Expr::Range { .. }
        | Expr::Index { .. }
        | Expr::TupleIndex { .. }
        | Expr::Path(_)
        | Expr::StructInit { .. }
        | Expr::ListComprehension { .. }
        | Expr::DictComprehension { .. }
        | Expr::Slice { .. }
        | Expr::Spread(_)
        | Expr::DictSpread(_) => {
            collections::eval_collection_expr(expr, env, functions, classes, enums, impl_methods).transpose()
        }
        // A struct-update spread is consumed by the constructor that owns it
        // (interpreter_call/core/class_instantiation.rs). Reaching generic
        // expression evaluation means `..base` was written somewhere it has no
        // meaning; say so instead of evaluating the base and silently using it
        // as an ordinary value.
        Expr::StructSpread(_) => Some(Err(CompileError::semantic(
            "struct spread `..base` is only valid as an argument of a struct/class construction \
             such as `S(..base, field: value)`"
                .to_string(),
        ))),
        // Remaining variants (Spawn, Await, Yield, Try, MacroInvocation, Unwrap*, etc.)
        // are handled by the match in evaluate_expr.
        _ => None,
    }
}

/// Evaluate a constant expression at compile time
pub(crate) fn evaluate_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Check watchdog timeout at every expression evaluation (single atomic load, negligible overhead).
    if crate::interpreter::is_timeout_exceeded() {
        return Err(CompileError::TimeoutExceeded {
            timeout_secs: crate::interpreter::timeout_limit_secs(),
        });
    }

    // Phase D dispatch profiler: default OFF (one relaxed atomic load when off).
    crate::interpreter::dispatch_profile::record(expr);

    // Fast path: O(1) discriminant-based dispatch — avoids up to 4 sequential
    // full-enum matches when the previous cascade approach returned None.
    if let Some(result) = route_expr(expr, env, functions, classes, enums, impl_methods) {
        return result;
    }

    match expr {
        Expr::Spawn(inner) => Ok(spawn_actor_with_expr(
            inner,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )),
        Expr::Await(inner) => {
            check_effect_violations("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => f.await_result().map_err(|e| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::AWAIT_FAILED)
                        .with_help("ensure the future completes successfully");
                    CompileError::semantic_with_context(format!("await failed: {}", e), ctx)
                }),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::AWAIT_FAILED)
                            .with_help("ensure the actor completes successfully");
                        CompileError::semantic_with_context(format!("await failed: {}", e), ctx)
                    })?;
                    Ok(Value::Nil)
                }
                _ => {
                    // Eager-async semantics: the interpreter evaluates async fn
                    // bodies eagerly, so `await f()` receives the already-resolved
                    // value (or a Simple-level Promise object). await_value extracts
                    // resolved Promises and passes plain values through unchanged —
                    // erroring here broke every direct `await async_fn()` call.
                    crate::interpreter::async_support::await_value(val)
                }
            }
        }
        Expr::Yield(maybe_val) => {
            let yield_val = match maybe_val {
                Some(expr) => evaluate_expr(expr, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };

            let added = GENERATOR_YIELDS.with(|cell| {
                if let Some(yields) = cell.borrow_mut().as_mut() {
                    yields.push(yield_val.clone());
                    true
                } else {
                    false
                }
            });

            if !added {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("yield can only be used inside a generator function");
                return Err(CompileError::semantic_with_context(
                    "invalid operation: yield called outside of generator",
                    ctx,
                ));
            }

            Ok(Value::Nil)
        }
        Expr::MacroInvocation { name, args: macro_args } => {
            let result = evaluate_macro_invocation(name, macro_args, env, functions, classes, enums, impl_methods)?;

            // Register symbols introduced by macro contracts (#1303)
            if let Some(mut introduced) = take_macro_introduced_symbols() {
                // Register introduced functions
                for (func_name, func_def) in introduced.introduced_functions {
                    functions.insert(func_name, func_def);
                }

                // Register introduced classes
                for (class_name, class_def) in introduced.introduced_classes {
                    classes.insert(class_name, class_def);
                }

                // Register introduced types (stored as Nil for now)
                for (name, _ty) in introduced.introduced_types {
                    env.insert(name, Value::Nil);
                }

                // Register introduced variables
                for (name, _ty, _is_const) in introduced.introduced_vars {
                    let value = introduced.introduced_var_values.remove(&name).unwrap_or(Value::Nil);
                    env.insert(name, value);
                }

                // NOTE: Inject code execution is FULLY IMPLEMENTED in macro/expansion.rs
                // - MacroAnchor::Here blocks execute immediately at callsite (line 138-141)
                // - MacroAnchor::Head blocks execute immediately with a trace warning (line 130-137)
                // - MacroAnchor::Tail blocks queue via queue_tail_injection() (line 125-129)
                //   and execute at block exit via exit_block_scope() (interpreter.rs:658-671)
                //
                // The inject labels from contracts are used to route emit blocks to the
                // correct execution path based on their anchor type.
            }

            Ok(result)
        }
        Expr::Try(inner) => {
            // Try operator: expr? - unwrap Ok or propagate Err
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) => {
                    match ResultVariant::from_name(variant) {
                        Some(ResultVariant::Ok) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(ResultVariant::Err) => {
                            // Return the Err as a TryError that should be propagated
                            Err(CompileError::TryError(Box::new(val)))
                        }
                        None => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_PATTERN)
                                .with_help("Result variants are Ok and Err");
                            Err(CompileError::semantic_with_context(
                                format!("invalid pattern: invalid Result variant: {}", variant),
                                ctx,
                            ))
                        }
                    }
                }
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) => {
                    match OptionVariant::from_name(variant) {
                        Some(OptionVariant::Some) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(OptionVariant::None) => {
                            // Return None as a TryError
                            Err(CompileError::TryError(Box::new(val)))
                        }
                        None => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_PATTERN)
                                .with_help("Option variants are Some and None");
                            Err(CompileError::semantic_with_context(
                                format!("invalid pattern: invalid Option variant: {}", variant),
                                ctx,
                            ))
                        }
                    }
                }
                // `nil` is the interpreter's representation of Option::None
                // (see `try_unwrap_option_or_result`, which maps Value::Nil to
                // "absent"). `return nil` from an `-> Option<T>` function must
                // therefore propagate through `?` exactly like an explicit None.
                Value::Nil => Err(CompileError::TryError(Box::new(Value::Nil))),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("try operator (?) can only be used on Result or Option types");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: ? operator requires Result or Option type, got {}",
                            val.type_name()
                        ),
                        ctx,
                    ))
                }
            }
        }
        // Force unwrap: expr! - unwrap Option/Result or panic
        Expr::ForceUnwrap(inner) => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("force unwrap (!) can only be used on Some/Ok values; got None/Err");
                Err(CompileError::semantic_with_context(
                    format!(
                        "force unwrap failed: expected Some or Ok, got {}",
                        val.to_display_string()
                    ),
                    ctx,
                ))
            }
        }
        // Existence check: expr.? - returns T? (the value itself if present, nil if absent).
        // "Present" means: not nil, and (for Option/Result) Some/Ok, and (for
        // collections/strings) non-empty. See
        // doc/07_guide/quick_reference/syntax_quick_reference.md "Existence Check (`.?`)".
        //
        // This intentionally returns the *value* (or `Value::Nil`), not a
        // bool: `.? ??`, `.?` chaining, and `if val v = expr.?:` all rely on
        // getting the real unwrapped value back (see
        // test/03_system/feature/usage/exists_check_value_return_spec.spl).
        // `is_present` is computed correctly here (Option/Result presence
        // comes from `try_unwrap_option_or_result`'s Some/Ok-vs-None/Err
        // check, not from the payload's truthiness -- a bare `Int`/`Bool`/
        // `Float` payload always falls through to the `_ => true` arm below
        // regardless of its value). The "0 is falsy" landmine
        // (doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md)
        // is NOT here: it is in callers that take this correct "value or
        // Value::Nil" result and run it back through generic
        // `Value::truthy()` (which treats `Int(0)`/`Bool(false)`/`""` as
        // falsy) instead of a simple "is it `Value::Nil`" presence check.
        // See `is_condition_present` in `interpreter_control.rs` for the fix
        // at those call sites.
        Expr::ExistsCheck(inner) => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            // First unwrap any Option/Result layer (Some/Ok -> payload, None/Err/Nil -> absent).
            // This also makes `opt.?` a pass-through onto the same nilable representation
            // used elsewhere in the interpreter (raw value or Value::Nil).
            let unwrapped = try_unwrap_option_or_result(&val);
            let result = match unwrapped {
                Some(v) => {
                    let is_present = match &v {
                        Value::Nil => false,
                        // Empty collections are not present
                        Value::Array(arr) => !arr.is_empty(),
                        Value::Dict(dict) => !dict.is_empty() || crate::interpreter::module_dict_len(dict) != 0,
                        // Empty strings are not present, unless an explicit `Some("")`
                        // wrapper says a text value exists (it just happens to be empty).
                        Value::Str(s) => {
                            !s.is_empty()
                                || matches!(&val, Value::Enum { enum_name, variant, .. }
                                    if enum_name == "Option" && variant == "Some")
                        }
                        // Objects with class "Set" - check if inner items are empty
                        Value::Object { class, fields } if class == "Set" => {
                            // Set is typically stored with an "items" field containing a Dict
                            if let Some(Value::Dict(items)) = fields.get("items") {
                                !items.is_empty()
                            } else {
                                true // If no items field, treat as present
                            }
                        }
                        // All other values (numbers, bools, structs, etc.) are present
                        _ => true,
                    };
                    if is_present {
                        v
                    } else {
                        Value::Nil
                    }
                }
                None => Value::Nil,
            };
            Ok(result)
        }
        // Safe unwrap: expr unwrap or: default
        Expr::UnwrapOr { expr: inner, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                evaluate_expr(default, env, functions, classes, enums, impl_methods)
            }
        }
        // Safe unwrap with lazy default: expr unwrap else: closure
        Expr::UnwrapElse {
            expr: inner,
            fallback_fn,
        } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                // Evaluate the fallback closure and call it
                let closure = evaluate_expr(fallback_fn, env, functions, classes, enums, impl_methods)?;
                call_closure_no_args(closure, env, functions, classes, enums, impl_methods)
            }
        }
        // Safe unwrap or early return: expr unwrap or_return: default
        Expr::UnwrapOrReturn { expr: inner, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                // Evaluate the caller-supplied default and return it (early
                // return from the enclosing function), rather than
                // propagating the None/Err receiver like `?` does.
                let default_val = evaluate_expr(default, env, functions, classes, enums, impl_methods)?;
                Err(CompileError::TryError(Box::new(default_val)))
            }
        }
        // Null coalescing: expr ?? default
        Expr::Coalesce { expr: inner, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                evaluate_expr(default, env, functions, classes, enums, impl_methods)
            }
        }
        // Optional chaining: expr?.field / expr?.method(args).
        // Contract (syntax_quick_reference.md § Safe Navigation, and the
        // self-hosted `optional_chain_desugar` in
        // src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl):
        // the result is the member's value AS-IS when the receiver is present
        // (Some/Ok payload unwrapped; any other value is itself), else nil.
        // It is never re-wrapped, so `x?.maybe(0) ?? d` sees the method's own
        // None and `a?.next?.next?.v` sees a plain nil field. Wrapping here
        // produced Some(None)/Some(nil) and diverged from JIT + native.
        Expr::OptionalChain { expr: inner, field } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match try_unwrap_option_or_result(&val) {
                // Read the member through the ordinary `.field` evaluator so
                // every receiver kind (ClassInstance, Object, Dict, properties)
                // behaves exactly like `payload.field`.
                Some(unwrapped) => with_optional_chain_temp(env, unwrapped, |env, recv| {
                    let access = Expr::FieldAccess {
                        receiver: recv,
                        field: field.clone(),
                    };
                    evaluate_expr(&access, env, functions, classes, enums, impl_methods)
                }),
                None => Ok(Value::Nil),
            }
        }
        Expr::OptionalMethodCall { receiver, method, args } => {
            let val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?;
            match try_unwrap_option_or_result(&val) {
                Some(unwrapped) => with_optional_chain_temp(env, unwrapped, |env, recv| {
                    evaluate_method_call(&recv, method, args, env, functions, classes, enums, impl_methods)
                }),
                None => Ok(Value::Nil),
            }
        }
        // Safe cast with default: expr as Type or: default
        Expr::CastOr {
            expr: inner,
            target_type,
            default,
        } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => evaluate_expr(default, env, functions, classes, enums, impl_methods),
            }
        }
        // Safe cast with lazy default: expr as Type else: closure
        Expr::CastElse {
            expr: inner,
            target_type,
            fallback_fn,
        } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => {
                    let closure = evaluate_expr(fallback_fn, env, functions, classes, enums, impl_methods)?;
                    call_closure_no_args(closure, env, functions, classes, enums, impl_methods)
                }
            }
        }
        // Safe cast or early return: expr as Type or_return:
        Expr::CastOrReturn {
            expr: inner,
            target_type,
        } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => {
                    // Return None to signal early return
                    let none_val = Value::Enum {
                        enum_name: enum_names::OPTION.to_string(),
                        variant: enum_names::NONE.to_string(),
                        payload: None,
                    };
                    Err(CompileError::TryError(Box::new(none_val)))
                }
            }
        }
        // Contract expressions - not supported in interpreter yet
        Expr::ContractResult => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("contract 'result' keyword can only be used in contract blocks");
            Err(CompileError::semantic_with_context(
                "invalid operation: contract 'result' keyword can only be used in contract blocks".to_string(),
                ctx,
            ))
        }
        Expr::ContractOld(_) => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("contract old() expression can only be used in ensures blocks");
            Err(CompileError::semantic_with_context(
                "invalid operation: contract old() expression can only be used in ensures blocks".to_string(),
                ctx,
            ))
        }
        #[allow(unreachable_patterns)]
        // reason: exhaustive match guard; retained for forward-compatibility when new variants are added
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("this expression type is not supported in this context");
            Err(CompileError::semantic_with_context(
                format!("invalid operation: unsupported expression type: {:?}", expr),
                ctx,
            ))
        }
    }
}
