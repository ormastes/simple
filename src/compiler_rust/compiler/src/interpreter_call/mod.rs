// Call expression evaluation (main dispatcher)

mod bdd;
mod block_execution;
mod builtins;
mod core;
mod mock;

// Re-export public items
pub use bdd::{clear_bdd_state, get_ignored_tests, get_test_results};
pub use core::clear_class_instantiation_state;
pub(crate) use bdd::{
    exec_block_value, BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_EXPECT_FAILED,
    BDD_EXPECT_PROVISIONAL, BDD_EXPECT_SEQ, BDD_FAILURE_MSG, BDD_INDENT, BDD_LAZY_VALUES, BDD_MATCHER_COUNT,
    BDD_MATCHER_RAN, BDD_PROVISIONAL_SEQ,
    BDD_SHARED_EXAMPLES,
};
pub(crate) use core::{
    bind_args, bind_args_with_injected, bind_args_with_values, captured_env_with_live_globals, exec_function, exec_function_with_bound_args,
    exec_function_with_captured_env, exec_function_with_values, exec_function_with_values_and_self, exec_lambda,
    execute_function_body, instantiate_class, publish_and_repoint, publish_live_bound_globals, refresh_live_bound_globals,
    sync_live_bound_globals, sync_owned_captured_globals, ProceedContext, IN_NEW_METHOD,
};
pub(crate) use core::bitfield_support::instantiate_bitfield_from_args;

use std::sync::Arc;
use std::borrow::Borrow;
use std::io::Write;
use std::path::Path;
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    call_extern_function, dispatch_context_method, evaluate_expr, BUILTIN_CHANNEL, CONTEXT_OBJECT, EXTERN_FUNCTIONS,
    CLASS_OVERLOADS, FUNCTION_OVERLOADS, GLOBAL_ENUMS, GLOBAL_IMPL_METHODS, BITFIELDS, CURRENT_EXEC_MODULE,
    FUNCTION_MODULE_OWNER,
};
use crate::interpreter::module_cache::MODULE_CLASSES_CACHE;
use crate::runtime_profile;
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef, Type};
use std::collections::HashMap;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

const METHOD_SELF: &str = "self";

/// Cached `SIMPLE_DEBUG_OVERLOAD_SELECT` flag. This is read on the hot overload-
/// resolution path (per candidate, per param, and recursively per array element),
/// where calling `std::env::var_os` every time is pathologically slow — it locks
/// the process environment and allocates on each call, which stalled interpreted
/// native-build for minutes. The flag never changes during a run, so read it once.
fn debug_overload_select() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var_os("SIMPLE_DEBUG_OVERLOAD_SELECT").is_some())
}

fn value_type_matches_name(value: &Value, expected: &str) -> bool {
    let matched = value.type_name() == expected
        || value.matches_type(expected)
        || matches!((value, expected), (Value::Str(_), "text"));
    if debug_overload_select() {
        println!(
            "[type-match] expected={expected} runtime={} display={} matched={matched}",
            value.type_name(),
            value.to_display_string()
        );
    }
    matched
}

fn value_matches_type(value: &Value, ty: &Type) -> bool {
    match ty {
        Type::Simple(name) | Type::Generic { name, .. } => value_type_matches_name(value, name),
        Type::Array { element, .. } => match value {
            // Overload scoring runs this per candidate, per call. Simple arrays
            // are homogeneous (every element of a `[T]` value shares element
            // type), so the first element is representative — testing it is
            // equivalent to testing all of them, and an empty array matches any
            // element type exactly as `.all()` over an empty slice did (true).
            // The old exhaustive `items.iter().all(..)` walk made overload
            // dispatch O(array_len) PER CANDIDATE: an Engine2D erased-receiver
            // method call whose scored values include a large backing buffer (a
            // framebuffer pixel array) cost 1+ second each and scaled with the
            // impl/candidate count — the interpreter dispatch cliff
            // (doc/08_tracking/bug/showcase_lanes_regressions_2026-07-18.md
            // item 6, bisected to a10935e78a). Bounding this to O(1) removes the
            // cliff without changing which overload is selected for homogeneous
            // arrays.
            Value::Array(items) => items.first().is_none_or(|item| value_matches_type(item, element)),
            Value::FrozenArray(items) => items.first().is_none_or(|item| value_matches_type(item, element)),
            // Tuples may be heterogeneous, but are bounded by (small) declared
            // arity rather than data size, so keep the exhaustive check to
            // preserve dispatch semantics for tuple-as-array-argument matches.
            Value::Tuple(items) => items.iter().all(|item| value_matches_type(item, element)),
            _ => false,
        },
        _ => true,
    }
}

fn overload_score(func: &FunctionDef, values: &[Value]) -> Option<usize> {
    if func.params.len() != values.len() {
        return None;
    }

    let debug_overloads = debug_overload_select();
    let mut score = 0usize;
    for (param, value) in func.params.iter().zip(values.iter()) {
        if debug_overloads {
            println!(
                "[overload] fn={} param={} ty={:?} value_type={} value={}",
                func.name,
                param.name,
                param.ty,
                value.type_name(),
                value.to_display_string()
            );
        }
        if let Some(ty) = &param.ty {
            if !value_matches_type(value, ty) {
                if debug_overloads {
                    println!("[overload]   -> no match");
                }
                return None;
            }
            score += match ty {
                Type::Array { .. } => 4,
                Type::Simple(_) | Type::Generic { .. } => 2,
                _ => 1,
            };
        }
    }
    if debug_overloads {
        println!("[overload]   -> score={score}");
    }
    Some(score)
}

/// Identity-keyed lookup into `FUNCTION_MODULE_OWNER` (see its doc comment):
/// `None` when this candidate's owning module was never recorded (e.g. a
/// struct's mangled static-method overload registration doesn't tag one).
fn function_module_owner(func: &Arc<FunctionDef>) -> Option<Arc<str>> {
    let key = Arc::as_ptr(func) as usize;
    FUNCTION_MODULE_OWNER
        .with(|cell| cell.borrow().get(&key).cloned())
        .or_else(|| {
            func.attributes.iter().find_map(|attribute| {
                attribute
                    .name
                    .strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)
                    .map(|raw| {
                        Arc::from(
                            crate::interpreter::normalize_path_key(Path::new(raw))
                                .to_string_lossy()
                                .as_ref(),
                        )
                    })
            })
        })
}

/// Every registered definition of `name`: the overload set plus the flat-map
/// entry (which is not always in the overload set).
fn all_candidates(name: &str, functions: &HashMap<String, Arc<FunctionDef>>) -> Vec<Arc<FunctionDef>> {
    let mut out = FUNCTION_OVERLOADS.with(|cell| cell.borrow().get(name).cloned()).unwrap_or_default();
    if let Some(flat) = functions.get(name) {
        if !out.iter().any(|c| Arc::ptr_eq(c, flat)) {
            out.push(Arc::clone(flat));
        }
    }
    out
}

/// The definition of `name` DECLARED BY `owner`, if exactly that one exists.
fn candidate_declared_by(
    owner: &str,
    name: &str,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Option<Arc<FunctionDef>> {
    all_candidates(name, functions)
        .into_iter()
        .find(|candidate| function_module_owner(candidate).is_some_and(|o| *o == *owner))
}

/// True when `func`'s owning module matches the module of the function whose
/// body is currently executing. False (never preferred) when either side is
/// unknown, so callers with no module info behave exactly as before.
fn is_current_module_candidate(func: &Arc<FunctionDef>) -> bool {
    let current = CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    let owner = function_module_owner(func);
    if debug_overload_select() {
        println!("[module-tie] fn={} current={:?} owner={:?}", func.name, current, owner);
    }
    match (current, owner) {
        (Some(cur), Some(owner)) => cur == owner,
        _ => false,
    }
}

fn select_overload(candidates: &[Arc<FunctionDef>], values: &[Value]) -> Option<Arc<FunctionDef>> {
    let mut best: Option<(usize, Arc<FunctionDef>)> = None;
    for func in candidates {
        if let Some(score) = overload_score(func, values) {
            match &best {
                // Exact tie: keep the existing first-registered candidate
                // UNLESS the new one is the candidate defined in the calling
                // function's own module and the current best is not — this
                // is the sole behavior change from the historical
                // "keep first on tie" rule, scoped to fix the cross-module
                // unqualified same-name/same-arity collision (see
                // doc/08_tracking/bug/interp_cross_module_struct_field_collision_2026-07-04.md).
                // When module ownership is unknown for either candidate,
                // `is_current_module_candidate` is false for both and this
                // arm is a no-op, so untagged call sites are unaffected.
                Some((best_score, best_func)) if *best_score == score => {
                    if !is_current_module_candidate(best_func) && is_current_module_candidate(func) {
                        best = Some((score, Arc::clone(func)));
                    }
                }
                Some((best_score, _)) if *best_score > score => {}
                _ => best = Some((score, Arc::clone(func))),
            }
        }
    }
    best.map(|(_, func)| func)
}

fn select_named_static_overload<'a, I, F>(
    candidates: I,
    method_name: &str,
    values: &[Value],
) -> Option<Arc<FunctionDef>>
where
    I: IntoIterator<Item = &'a F>,
    F: Borrow<FunctionDef> + 'a,
{
    let named: Vec<Arc<FunctionDef>> = candidates
        .into_iter()
        .filter_map(|func| {
            let func = func.borrow();
            let is_static = func.is_static || !func.params.iter().any(|param| param.name == METHOD_SELF);
            if func.name == method_name && is_static {
                Some(Arc::new(func.clone()))
            } else {
                None
            }
        })
        .collect();

    if debug_overload_select() {
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/tmp/simple_overload_debug.log")
        {
            let _ = writeln!(
                file,
                "method={method_name} candidates={} values={:?}",
                named.len(),
                values.iter().map(|v| v.type_name()).collect::<Vec<_>>()
            );
            for func in &named {
                let _ = writeln!(
                    file,
                    "  fn={} params={:?}",
                    func.name,
                    func.params.iter().map(|p| &p.ty).collect::<Vec<_>>()
                );
            }
        }
    }

    match named.len() {
        0 => None,
        1 => named.into_iter().next(),
        _ => select_overload(&named, values),
    }
}

/// Dispatch an already-evaluated `Value` as a callable.
///
/// Returns `Ok(Some(result))` when `val` was callable and the call was made,
/// and `Ok(None)` when `val` is not callable so the caller can continue its own
/// resolution chain. This is the single place that knows which `Value` variants
/// are invocable; both the bare-identifier callee path and the field-access
/// callee path route through it so `f(x)`, `(self.f)(x)` and `(obj.f)(x)` agree.
pub(crate) fn call_value_as_callable(
    val: Value,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Callable objects use the `__call__` protocol and need `val` by reference,
    // so they are handled before the by-value match below takes ownership.
    if matches!(val, Value::Object { .. }) {
        let evaluated_args: Vec<Value> = args
            .iter()
            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
            .collect::<Result<Vec<_>, _>>()?;
        return super::interpreter_control::call_method_if_exists(
            &val,
            "__call__",
            &evaluated_args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        );
    }

    match val {
        Value::Function { def, captured_env, .. } => {
            let mut captured_env_clone = Env::clone(&captured_env);
            Ok(Some(core::exec_function_with_captured_env(
                &def,
                args,
                env,
                &mut captured_env_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )?))
        }
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut captured_clone = Env::clone(&captured);
            Ok(Some(core::exec_lambda(
                &params,
                &body,
                args,
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )?))
        }
        Value::Constructor { class_name } => Ok(Some(core::instantiate_class(
            &class_name,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?)),
        // Calling a generator returns the next yielded value (or Nil if exhausted)
        Value::Generator(gen) => Ok(Some(gen.next().unwrap_or(Value::Nil))),
        Value::NativeFunction(native) => {
            let evaluated: Vec<Value> = args
                .iter()
                .map(|a| {
                    if a.name.is_some() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("native functions do not support named arguments");
                        return Err(CompileError::semantic_with_context(
                            "native function does not support named arguments".to_string(),
                            ctx,
                        ));
                    }
                    evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Some((native.func)(&evaluated)?))
        }
        _ => Ok(None),
    }
}

#[allow(clippy::borrowed_box)] // reason: Box<dyn Trait> is the required storage type for this dispatch point
thread_local! {
    /// Prelude names already reported by `warn_prelude_shadow_once`, so a
    /// shadowed builtin called in a loop warns once rather than per call.
    static PRELUDE_SHADOW_WARNED: std::cell::RefCell<std::collections::HashSet<String>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Priority-2 precedence: does the free-function builtin `name` win over a
/// same-named user definition?
///
/// A user-defined module-level `fn` wins, except for process-control names in
/// `PRELUDE_UNSHADOWABLE`.
/// See doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md
pub fn builtin_wins_over_user_fn(name: &str, user_defined: bool) -> bool {
    !user_defined || super::interpreter_eval::PRELUDE_UNSHADOWABLE.contains(&name)
}

#[cfg(test)]
mod precedence_tests {
    use super::builtin_wins_over_user_fn;

    /// doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md:
    /// a module-level `fn freeze`/`fn len` must beat the interpreter builtin.
    #[test]
    fn user_defined_function_wins_over_builtin() {
        assert!(builtin_wins_over_user_fn("freeze", false));
        assert!(builtin_wins_over_user_fn("len", false));
        assert!(!builtin_wins_over_user_fn("freeze", true));
        assert!(!builtin_wins_over_user_fn("len", true));
        for name in crate::interpreter::PRELUDE_UNSHADOWABLE {
            assert!(builtin_wins_over_user_fn(name, true));
        }
    }
}

/// Report, once per name, that a user `fn` shadows a prelude builtin.
///
/// `fenced` distinguishes the two policies: a `PRELUDE_UNSHADOWABLE` name is
/// reported as *ignored* (the builtin still wins), any other prelude name is
/// reported as an *active* rebind so the hijack is at least visible.
///
/// Silenced by `SIMPLE_NO_PRELUDE_SHADOW_WARNING=1` for lanes that knowingly
/// ship shims; it is a diagnostic, not a gate.
fn warn_prelude_shadow_once(name: &str, functions: &HashMap<String, Arc<FunctionDef>>, fenced: bool) {
    if std::env::var("SIMPLE_NO_PRELUDE_SHADOW_WARNING").as_deref() == Ok("1") {
        return;
    }
    let first = PRELUDE_SHADOW_WARNED.with(|c| c.borrow_mut().insert(name.to_string()));
    if !first {
        return;
    }
    let where_ = functions
        .get(name)
        .map(|f| format!("line {}", f.span.line))
        .unwrap_or_else(|| "an overloaded definition".to_string());
    if fenced {
        eprintln!(
            "WARNING: `fn {name}` at {where_} shadows the prelude builtin `{name}`, \
             which is process-control and cannot be rebound -- the builtin is being used. \
             Rename the local function."
        );
    } else {
        eprintln!(
            "WARNING: `fn {name}` at {where_} shadows the prelude builtin `{name}` \
             and is being called INSTEAD of it. This applies to the whole program, \
             including modules that only imported this one transitively. Rename the \
             local function if that was not intended."
        );
    }
}

pub(crate) fn evaluate_call(
    callee: &Box<Expr>,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Priority 1: Check extern functions first (before builtins)
    if let Expr::Identifier(name) = callee.as_ref() {
        let is_extern = EXTERN_FUNCTIONS.with(|cell| {
            let externs = cell.borrow();
            let contains = externs.contains(name);
            if crate::is_debug_mode() && !contains && name.contains("_box_") {
                eprintln!("[DEBUG] Looking for '{}' in EXTERN_FUNCTIONS: {}", name, contains);
                eprintln!("[DEBUG] EXTERN_FUNCTIONS contains {} functions", externs.len());
                if externs.len() < 50 {
                    eprintln!("[DEBUG] Functions: {:?}", externs.iter().take(10).collect::<Vec<_>>());
                }
            }
            contains
        });
        // `EXTERN_FUNCTIONS` is seeded in bulk from the runtime's full symbol
        // manifest (`RUNTIME_SYMBOL_NAMES`, see interpreter_eval.rs), not just
        // from `extern fn` declarations actually parsed out of the running
        // program. That means a name can land in `EXTERN_FUNCTIONS` purely by
        // coincidentally matching a runtime symbol (e.g. `rt_array_len_safe`,
        // a local pure-Simple generic helper in lexer.spl/parser.spl that
        // happens to share its name with an unrelated Rust runtime export).
        // A local (possibly generic) function definition in scope must win
        // over that coincidental extern registration — only fall back to
        // extern dispatch when no local definition exists. See
        // doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md.
        //
        // HOWEVER: `PRELUDE_EXTERN_FUNCTIONS` (print/exit/abs/...) lands in the
        // same `EXTERN_FUNCTIONS` set as those coincidental runtime symbols, so
        // this hatch used to apply to prelude builtins too -- a top-level
        // `fn exit` anywhere in the *transitive* import closure silently rebound
        // `exit` for the whole program. Two fences now apply:
        //   1. `PRELUDE_UNSHADOWABLE` names (process control) ignore the hatch
        //      entirely and always reach the builtin.
        //   2. Any other user-facing prelude name that IS shadowed warns once,
        //      naming the builtin and the shadowing definition's line.
        // See doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md
        let mut has_local_def = is_extern
            && (functions.contains_key(name.as_str())
                || FUNCTION_OVERLOADS.with(|cell| cell.borrow().contains_key(name.as_str())));
        if has_local_def && super::interpreter_eval::is_user_facing_prelude(name.as_str()) {
            if super::interpreter_eval::PRELUDE_UNSHADOWABLE.contains(&name.as_str()) {
                // Fence: the builtin always wins for process-control names.
                has_local_def = false;
                warn_prelude_shadow_once(name.as_str(), functions, true);
            } else {
                warn_prelude_shadow_once(name.as_str(), functions, false);
            }
        }
        if is_extern && !has_local_def {
            if runtime_profile::is_profiling_active() {
                runtime_profile::record_full_call(name, None, vec![], runtime_profile::CallType::Ffi);
            }
            let result = call_extern_function(name, args, env, functions, classes, enums, impl_methods);
            if runtime_profile::is_profiling_active() {
                runtime_profile::record_full_return(None);
            }
            return result;
        }

        // Priority 2: Try built-ins.
        //
        // NOTE: this used to claim "so builtins can't be shadowed". That was
        // FALSE for every prelude name the Priority-1 hatch above reaches: when
        // `has_local_def` was true the extern/builtin dispatch was skipped and
        // control fell through to the user function at Priority 4. Measured
        // 2026-08-10: 50 of the 51 user-facing prelude names were rebindable by
        // a transitively-imported top-level `fn` in the interpreter lane (43 of
        // 51 in the JIT lane). The fences added at Priority 1 are what actually
        // protects the names listed in `PRELUDE_UNSHADOWABLE`; every other
        // prelude name remains shadowable *by design*, but now warns.
        //
        // 2026-08-21: a user-defined module-level `fn` of the same name now
        // wins over a free-function builtin (`freeze`, `len`, ...), except for
        // process-control names in `PRELUDE_UNSHADOWABLE`. The gate is on the
        // CALL, not on its result: several `eval_builtin` arms evaluate their
        // arguments and have side effects. Warn once so it is never silent.
        // See doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md
        let user_defined = functions.contains_key(name.as_str())
            || FUNCTION_OVERLOADS.with(|cell| cell.borrow().contains_key(name.as_str()));
        let builtin_wins = builtin_wins_over_user_fn(name.as_str(), user_defined);
        if user_defined
            && !builtin_wins
            && super::interpreter_eval::is_user_facing_prelude(name.as_str())
        {
            warn_prelude_shadow_once(name.as_str(), functions, false);
        }
        if builtin_wins {
            if let Some(result) =
                builtins::eval_builtin(name, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }

        // Priority 3: Try BDD framework for spec DSL names (describe/it/before_each/…).
        //
        // This MUST run before `functions.get(name)` below because the spec DSL in
        // `std/spec/dsl.spl` defines overloaded functions (e.g. `fn it(desc, block)` and
        // `fn it(desc, enabled, block)`) and the interpreter's function registry is a
        // flat `HashMap<String, Arc<FunctionDef>>` that overwrites prior entries on
        // name collision. That makes the 2-arg variants unreachable via
        // `functions.get`, causing `bind_args` to fail with
        // "function expects argument for parameter 'block'" whenever a system spec
        // reaches the interpreter via `run_file_interpreted`. The BDD builtin path
        // short-circuits this by handling the DSL names directly and only returns
        // `Some` for names it actually recognizes, so non-DSL calls still fall
        // through to the user-function lookup unchanged.
        if let Some(result) = bdd::eval_bdd_builtin(name, args, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }

        // Priority 4: Check overloaded regular functions before the flat map fallback.
        let overloads = FUNCTION_OVERLOADS.with(|cell| cell.borrow().get(name).cloned());
        if let Some(overloads) = overloads {
            if overloads.len() > 1 {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(func) = select_overload(&overloads, &evaluated_args) {
                    return core::exec_function_with_values_and_writeback(
                        &func,
                        &evaluated_args,
                        args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
            }
        }

        // Priority 5: Check regular functions (user-defined) — most common case
        if let Some(func) = functions.get(name).cloned() {
            return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
        }

        // Try mock library
        if let Some(result) = mock::eval_mock_builtin(name, args, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }

        // Priority 6: Check env for decorated functions and closures (decorators store
        // the decorated version in env while the original remains in functions)
        if let Some(val) = env.get(name).cloned() {
            if let Some(result) = call_value_as_callable(val, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }

        // Check bitfield constructors (e.g., Flags(raw) instantiation)
        let is_bitfield = BITFIELDS.with(|cell| cell.borrow().contains_key(name));
        if is_bitfield {
            return core::bitfield_support::instantiate_bitfield_from_args(
                name,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            );
        }

        // Check class constructors (e.g., MyClass() instantiation)
        if classes.contains_key(name) {
            return core::instantiate_class(name, args, env, functions, classes, enums, impl_methods);
        }

        // Check context object
        let context_obj = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
        if let Some(ctx) = context_obj {
            return dispatch_context_method(&ctx, name, args, env, functions, classes, enums, impl_methods);
        }

        // An aliased import (`use m.{f as g}`) binds `g` in the IMPORTING
        // module only. Flattening already records that edge as an owner
        // binding (`record_flattened_import_binding`), but until now ONLY
        // globals ever consulted it: a CALL of `g` looked `g` up in
        // `functions`, missed, and fell straight through to E1002. That is why
        // `use std.io_runtime.{file_rename as runtime_file_rename}`
        // (src/lib/nogc_sync_mut/io/file_ops.spl:218) made every module
        // reaching `io/file_ops` die with
        // `function `runtime_file_rename` not found` -- including
        // `update_test_database`, which is why a fully passing
        // `simple test <dir>` still exited 1 and wrote no test DB.
        //
        // This is the interpreter-side half of the HIR fix in
        // `hir/lower/lowerer.rs::collect_flattened_import_aliases`
        // (c0c4e707789); that one taught CODEGEN to resolve the alias, this
        // teaches the INTERPRETER, and both read the SAME recorded binding so
        // they cannot disagree about which definition an alias names.
        //
        // Selection is by module OWNER, never by bare name. Flattening mangles
        // only `main`, so all four `file_rename` definitions share one bare
        // key; binding the alias to `functions["file_rename"]` picks whichever
        // landed there -- for `runtime_file_rename` that is `io/file_ops`'s own
        // one-line wrapper, i.e. the alias resolves back to its own caller and
        // recurses until `stack overflow: recursion depth 1000 exceeded in
        // function 'file_rename'`. Measured, not hypothetical. Matching
        // `function_module_owner` against the binding's owner is what makes the
        // choice unambiguous; when no candidate matches we fall through to
        // E1002 rather than guess, because guessing is the defect above.
        if let Some(current) = CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone()) {
            if let Some((source_owner, source_name)) = crate::interpreter::owner_bindings(&current)
                .and_then(|bindings| bindings.get(name).cloned())
            {
                if std::env::var("SIMPLE_DEBUG_ALIAS").is_ok() {
                    eprintln!("[alias] name={name} current={current} source_owner={source_owner} source_name={source_name}");
                    for c in all_candidates(&source_name, functions) {
                        eprintln!("[alias]   cand {} owner={:?}", c.name, function_module_owner(&c));
                    }
                    eprintln!("[alias]   mangled={} present={}",
                        crate::interpreter::flatten_owner_mangled_name(&source_owner, &source_name),
                        functions.contains_key(&crate::interpreter::flatten_owner_mangled_name(&source_owner, &source_name)));
                    if let Some(b) = crate::interpreter::owner_bindings(&source_owner).and_then(|x| x.get(&source_name).cloned()) {
                        eprintln!("[alias]   next-hop={:?}", b);
                    } else {
                        eprintln!("[alias]   next-hop=NONE");
                    }
                }
                // MEASURED shape of this lookup (SIMPLE_DEBUG_ALIAS=1), for
                // `use std.io_runtime.{file_rename as runtime_file_rename}`:
                //
                //   current      = .../nogc_sync_mut/io/file_ops.spl
                //   source_owner = .../src/lib/io_runtime.spl        <- FACADE
                //   source_name  = file_rename
                //   candidates   = file_rename @ io/file_ops.spl     <- the CALLER's own wrapper
                //                  file_rename @ nogc_sync_mut/io_runtime.spl   <- the real one
                //                  (each registered twice)
                //   mangled(facade, file_rename) -> absent
                //   next hop from the facade -> (io/file_ops.spl, file_rename)
                //
                // Two facts drive the rule below, and both are why the earlier
                // attempts failed. (a) `source_owner` is the FACADE
                // `src/lib/io_runtime.spl`, never the declaring module, so
                // owner equality alone never matches. (b) The facade's own
                // binding for `file_rename` points BACK at `io/file_ops.spl`,
                // so following the chain walks straight into the caller's
                // wrapper and recurses until the stack overflows. The chain is
                // therefore NOT trustworthy here and is deliberately not walked.
                let mut target: Option<Arc<FunctionDef>> = functions
                    .get(&crate::interpreter::flatten_owner_mangled_name(&source_owner, &source_name))
                    .cloned()
                    .or_else(|| candidate_declared_by(&source_owner, &source_name, functions));

                if target.is_none() {
                    // An alias in module M can never legitimately denote M's own
                    // same-named function -- that is the wrapper whose body
                    // issued this very call -- so candidates owned by `current`
                    // are rejected outright. A candidate whose owner is UNKNOWN
                    // is also rejected: accepting unknown owners is exactly how
                    // the wrapper slipped back in through an `is_none_or` filter.
                    //
                    // Among what survives, prefer the module whose file stem
                    // matches the facade's (`src/lib/io_runtime.spl` ->
                    // `.../nogc_sync_mut/io_runtime.spl`), which is what a
                    // re-export facade actually names. Duplicate registrations
                    // of one module are common (see the dump above: two rows per
                    // owner), so this selects a MODULE, not a unique candidate.
                    let facade_stem = std::path::Path::new(&*source_owner).file_stem().map(|s| s.to_owned());
                    let mut outside: Vec<Arc<FunctionDef>> = all_candidates(&source_name, functions)
                        .into_iter()
                        .filter(|candidate| {
                            function_module_owner(candidate)
                                .is_some_and(|owner| *owner != *current)
                        })
                        .collect();
                    if let Some(stem) = facade_stem {
                        let matching: Vec<Arc<FunctionDef>> = outside
                            .iter()
                            .filter(|candidate| {
                                function_module_owner(candidate).is_some_and(|owner| {
                                    std::path::Path::new(&*owner).file_stem() == Some(stem.as_os_str())
                                })
                            })
                            .cloned()
                            .collect();
                        if !matching.is_empty() {
                            outside = matching;
                        }
                    }
                    // All survivors owned by ONE module means the choice is
                    // unambiguous even when that module registered several.
                    let owners: Vec<Arc<str>> =
                        outside.iter().filter_map(function_module_owner).collect();
                    if !owners.is_empty() && owners.iter().all(|o| *o == owners[0]) {
                        target = outside.into_iter().next();
                    }
                }

                if let Some(func) = target {
                    return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                }
            }
        }

        // If we reach here with an identifier name, the function is not found
        // E1002 - Undefined Function
        let known_names: Vec<&str> = functions.keys().map(|s| s.as_str()).collect();

        let suggestion = crate::error::typo::suggest_name(name, known_names.clone());
        let mut ctx = ErrorContext::new()
            .with_code(codes::UNDEFINED_FUNCTION)
            .with_help("check that the function is defined and in scope");

        // Every definition of this function may have been an inactive
        // `@cfg(<arch>)` variant stripped for the host target -- say so
        // instead of leaving a bare not-found (see pipeline::cfg_strip).
        if let Some(hint) = crate::pipeline::cfg_strip::stripped_fn_hint(name) {
            ctx = ctx.with_help(hint);
        }

        if let Some(best_match) = suggestion {
            ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
        }

        if !known_names.is_empty() && known_names.len() <= 5 {
            let names_list = known_names.join(", ");
            ctx = ctx.with_note(format!("available functions: {}", names_list));
        }

        return Err(CompileError::semantic_with_context(
            format!("function `{}` not found", name),
            ctx,
        ));
    }

    // Handle module-style calls: module.function()
    if let Expr::FieldAccess { receiver, field } = callee.as_ref() {
        if let Expr::Identifier(module_name) = receiver.as_ref() {
            // First, check if the receiver is a module dict in env
            if let Some(Value::Dict(module_dict)) = env.get(module_name).cloned() {
                // Look up function in the module's exports
                if let Some(func_val) = module_dict.get(field).cloned() {
                    if let Value::Function { def, captured_env, .. } = func_val {
                        let mut captured_env_clone = Env::clone(&captured_env);
                        return core::exec_function_with_captured_env(
                            &def,
                            args,
                            env,
                            &mut captured_env_clone,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        );
                    }
                    if let Value::Constructor { class_name } = func_val {
                        return core::instantiate_class(
                            &class_name,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        );
                    }
                }
            }
            // Map.new()/Dict.new() parse as FieldAccess rather than Path. Treat
            // the public aliases like the existing HashMap/BTreeMap builtins so
            // bootstrap code receives a genuinely empty dictionary instead of
            // falling through to receiver lookup or a synthetic `__type__` row.
            if field == "new" && matches!(module_name.as_str(), "Map" | "Dict" | "HashMap" | "BTreeMap") {
                return Ok(Value::Dict(std::sync::Arc::new(std::collections::HashMap::new())));
            }
            // Check for static method call on a type: Type.method()
            // This handles calls like Set.new() or Set.from_array()
            if field == "new" {
                let mut values = Vec::new();
                for arg in args {
                    values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                }
                if let Ok(value) = crate::interpreter::instantiate_bitfield(module_name, &values) {
                    return Ok(value);
                }
            }
            // Try local impl_methods first, then GLOBAL_IMPL_METHODS fallback
            let impl_methods_for_type = impl_methods
                .get(module_name)
                .cloned()
                .or_else(|| GLOBAL_IMPL_METHODS.with(|cell| cell.borrow().get(module_name).cloned()));
            if let Some(methods) = impl_methods_for_type {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(func) = select_named_static_overload(methods.iter(), field, &evaluated_args) {
                    // If calling a `new` method, mark it to prevent double execution via instantiate_class
                    let is_new_method = field == "new";
                    if is_new_method {
                        eprintln!("[WARN] Deprecated: {}.new() should be replaced with {}(). Use direct construction instead.", module_name, module_name);
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(module_name.to_string()));
                    }
                    let result = core::exec_function_with_values(
                        &func,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(module_name));
                    }
                    return result;
                }
            }
            // Check for class static methods
            if let Some(class_def) = classes.get(module_name).cloned() {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(func) = select_named_static_overload(class_def.methods.iter(), field, &evaluated_args) {
                    // If calling a `new` method, mark it to prevent double execution via instantiate_class
                    let is_new_method = field == "new";
                    if is_new_method {
                        eprintln!("[WARN] Deprecated: {}.new() should be replaced with {}(). Use direct construction instead.", module_name, module_name);
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(module_name.to_string()));
                    }
                    let result = core::exec_function_with_values(
                        &func,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(module_name));
                    }
                    return result;
                }
            }

            // Check for enum variant constructor: EnumName.Variant(args)
            // This handles calls like Result.Ok(42), Option.Some(x), etc.

            // Try local enums first, then GLOBAL_ENUMS fallback
            let enum_def_opt = enums
                .get(module_name)
                .cloned()
                .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(module_name).cloned()));
            if std::env::var("SCRATCH_WALL2_TRACE").is_ok() {
                eprintln!(
                    "[SCRATCH] module_name={} field={} local_enums_has={} global_enums_has={} enum_def_found={} variants={:?}",
                    module_name,
                    field,
                    enums.contains_key(module_name),
                    GLOBAL_ENUMS.with(|cell| cell.borrow().contains_key(module_name)),
                    enum_def_opt.is_some(),
                    enum_def_opt.as_ref().map(|d| d.variants.iter().map(|v| v.name.clone()).collect::<Vec<_>>())
                );
            }
            if let Some(enum_def) = enum_def_opt {
                if enum_def.variants.iter().any(|v| &v.name == field) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        Some(Box::new(evaluate_expr(
                            &args[0].value,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?))
                    } else {
                        let mut values = Vec::new();
                        for arg in args {
                            values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        Some(Box::new(Value::Tuple(values)))
                    };
                    // WRITE side of the enum-payload provenance diagnostic
                    // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                    // `EnumName.Variant(args)` construction path.
                    crate::interpreter::note_enum_payload_function_opt(
                        "variant-construction", &(module_name.clone()), &(field.clone()), &payload,
                    );
                    return Ok(Value::Enum {
                        enum_name: module_name.clone(),
                        variant: field.clone(),
                        payload,
                    });
                }
            }

            // Try block-scoped enums (defined in test blocks)
            if let Some(enum_def) =
                crate::interpreter::BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(module_name).cloned())
            {
                if enum_def.variants.iter().any(|v| &v.name == field) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        Some(Box::new(evaluate_expr(
                            &args[0].value,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?))
                    } else {
                        let mut values = Vec::new();
                        for arg in args {
                            values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        Some(Box::new(Value::Tuple(values)))
                    };
                    // WRITE side of the enum-payload provenance diagnostic
                    // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                    // `EnumName.Variant(args)` construction path.
                    crate::interpreter::note_enum_payload_function_opt(
                        "variant-construction", &(module_name.clone()), &(field.clone()), &payload,
                    );
                    return Ok(Value::Enum {
                        enum_name: module_name.clone(),
                        variant: field.clone(),
                        payload,
                    });
                }
            }

            // Fall back to global functions if module lookup failed
            if let Some(func) = functions.get(field).cloned() {
                return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(field) {
                return core::instantiate_class(field, args, env, functions, classes, enums, impl_methods);
            } else if let Some(Value::Function { def, captured_env, .. }) = env.get(field).cloned() {
                let mut captured_env_clone = Env::clone(&captured_env);
                return core::exec_function_with_captured_env(
                    &def,
                    args,
                    env,
                    &mut captured_env_clone,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                );
            }

            // Cross-module fallback for FieldAccess: search MODULE_CLASSES_CACHE
            // for the class definition when it's not in the local classes map.
            let cached_fa_class: Option<Arc<ClassDef>> = MODULE_CLASSES_CACHE.with(|cache| {
                let cache = cache.borrow();
                for (_path, module_classes) in cache.iter() {
                    if let Some(class_def) = module_classes.get(module_name.as_str()) {
                        return Some(class_def.clone());
                    }
                }
                None
            });
            if let Some(class_def) = cached_fa_class {
                classes.insert(module_name.clone(), class_def.clone());
                if let Some(func) = class_def.methods.iter().find(|m| &m.name == field) {
                    let is_new_method = field == "new";
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(module_name.to_string()));
                    }
                    let result = core::exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(module_name));
                    }
                    return result;
                }
            }

            // Last resort: try GLOBAL_IMPL_METHODS for impl methods that weren't
            // merged into the class definition (e.g., cross-module impl blocks,
            // or impl methods added after the class was cached)
            let global_impl_method: Option<Arc<FunctionDef>> = GLOBAL_IMPL_METHODS.with(|cell| {
                cell.borrow()
                    .get(module_name)
                    .and_then(|methods| methods.iter().find(|m| &m.name == field).cloned())
            });
            if let Some(func) = global_impl_method {
                let is_new_method = field == "new";
                if is_new_method {
                    core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(module_name.to_string()));
                }
                let result = core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                if is_new_method {
                    core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(module_name));
                }
                return result;
            }

            // Try the mangled free function name as a final fallback
            // (ClassName__method is registered when impl blocks are processed)
            let mangled_name = format!("{}__{}", module_name, field);
            if let Some(func) = functions.get(&mangled_name).cloned() {
                return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            }

            // Grouped field access used as a callee: `(self.cb)(x)` / `(obj.cb)(x)`.
            // The whole chain above assumes `module_name` names a module or class,
            // because that is how `module.function()` reaches here. But a
            // parenthesized call on a function-typed FIELD also lands here, and for
            // those the receiver is an ordinary in-scope value, not a module. The
            // unparenthesized `self.cb(x)` parses as a MethodCall and never reaches
            // this branch, which is why only the grouped form failed to resolve.
            // Evaluate the field and dispatch it through the same callable path a
            // bare `f(x)` uses; fall through to the error if it is not callable.
            if let Ok(field_val) = evaluate_expr(callee.as_ref(), env, functions, classes, enums, impl_methods) {
                if let Some(result) =
                    call_value_as_callable(field_val, args, env, functions, classes, enums, impl_methods)?
                {
                    return Ok(result);
                }
            }

            let ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_VARIABLE)
                .with_help("check that the symbol exists in the module");
            return Err(CompileError::semantic_with_context(
                format!("unknown symbol {}.{}", module_name, field),
                ctx,
            ));
        }
    }

    // Handle path calls: Type::method(args) or Type::Variant(args)
    if let Expr::Path(segments) = callee.as_ref() {
        if segments.len() == 2 {
            let type_name = &segments[0];
            let method_name = &segments[1];

            // Check bitfield constructor paths (e.g., Flags.new(raw))
            if method_name == "new" && BITFIELDS.with(|cell| cell.borrow().contains_key(type_name)) {
                return core::bitfield_support::instantiate_bitfield_from_args(
                    type_name,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                );
            }

            // Check if it's an enum variant constructor (local enums + GLOBAL_ENUMS fallback)
            let path_enum_def = enums
                .get(type_name)
                .cloned()
                .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(type_name).cloned()));
            if let Some(enum_def) = path_enum_def.as_ref() {
                if enum_def.variants.iter().any(|v| &v.name == method_name) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        Some(Box::new(evaluate_expr(
                            &args[0].value,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?))
                    } else {
                        let mut values = Vec::new();
                        for arg in args {
                            values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        Some(Box::new(Value::Tuple(values)))
                    };
                    // WRITE side of the enum-payload provenance diagnostic
                    // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                    // `EnumName.Variant(args)` construction path.
                    crate::interpreter::note_enum_payload_function_opt(
                        "variant-construction", &(type_name.clone()), &(method_name.clone()), &payload,
                    );
                    return Ok(Value::Enum {
                        enum_name: type_name.clone(),
                        variant: method_name.clone(),
                        payload,
                    });
                }
            }

            // Check for associated function call
            // Try local impl_methods first, then GLOBAL_IMPL_METHODS fallback
            let path_impl_methods = impl_methods
                .get(type_name)
                .cloned()
                .or_else(|| GLOBAL_IMPL_METHODS.with(|cell| cell.borrow().get(type_name).cloned()));
            if let Some(methods) = path_impl_methods {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(func) = select_named_static_overload(methods.iter(), method_name, &evaluated_args) {
                    // If calling a `new` method, mark it to prevent double execution via instantiate_class
                    let is_new_method = method_name == "new";
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(type_name.to_string()));
                    }
                    let result = core::exec_function_with_values(
                        &func,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(type_name));
                    }
                    return result;
                }
            }

            // The flat class registry is last-write-wins. If its same-named
            // type does not define this method, search the preserved class
            // definitions before any legacy bare-function fallback.
            let flat_class_has_method = classes
                .get(type_name)
                .map(|class_def| class_def.methods.iter().any(|method| method.name == *method_name))
                .unwrap_or(false);
            let path_overloaded_classes = CLASS_OVERLOADS.with(|cell| cell.borrow().get(type_name).cloned());
            if !flat_class_has_method {
                if let Some(class_defs) = path_overloaded_classes.as_ref() {
                    let evaluated_args: Vec<Value> = args
                        .iter()
                        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                        .collect::<Result<Vec<_>, _>>()?;
                    if let Some(func) = select_named_static_overload(
                        class_defs.iter().flat_map(|class_def| class_def.methods.iter()),
                        method_name,
                        &evaluated_args,
                    ) {
                        return core::exec_function_with_values(
                            &func,
                            &evaluated_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        );
                    }
                }
            }

            // Check for class associated function (static method)
            if let Some(class_def) = classes.get(type_name).cloned() {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(func) = select_named_static_overload(class_def.methods.iter(), method_name, &evaluated_args)
                {
                    // If calling a `new` method, mark it to prevent double execution via instantiate_class
                    let is_new_method = method_name == "new";
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(type_name.to_string()));
                    }
                    let result = core::exec_function_with_values(
                        &func,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(type_name));
                    }
                    return result;
                }
            }

            // A known type must not degrade `Span.empty()` into an unrelated
            // global `empty(shape)` call. Keep the legacy fallback only for
            // unresolved module-style receivers.
            let path_receiver_is_type = classes.contains_key(type_name)
                || path_overloaded_classes.is_some()
                || enums.contains_key(type_name)
                || GLOBAL_ENUMS.with(|cell| cell.borrow().contains_key(type_name))
                || BITFIELDS.with(|cell| cell.borrow().contains_key(type_name));
            if !path_receiver_is_type {
                if let Some(func) = functions.get(method_name).cloned() {
                    return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                } else if classes.contains_key(method_name) {
                    return core::instantiate_class(method_name, args, env, functions, classes, enums, impl_methods);
                }
            }

            // Special handling for built-in Option and Result types
            if type_name == "Option" && (method_name == "Some" || method_name == "None") {
                let payload = if method_name == "Some" {
                    if args.is_empty() {
                        return Err(CompileError::semantic("Option.Some requires one argument"));
                    }
                    Some(Box::new(evaluate_expr(
                        &args[0].value,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?))
                } else {
                    None
                };
                // WRITE side of the enum-payload provenance diagnostic
                // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                // `EnumName.Variant(args)` construction path.
                crate::interpreter::note_enum_payload_function_opt(
                    "variant-construction", &("Option".to_string()), &(method_name.clone()), &payload,
                );
                return Ok(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: method_name.clone(),
                    payload,
                });
            }

            if type_name == "Result" && (method_name == "Ok" || method_name == "Err") {
                if args.is_empty() {
                    return Err(CompileError::semantic(format!(
                        "Result.{} requires one argument",
                        method_name
                    )));
                }
                let payload = Some(Box::new(evaluate_expr(
                    &args[0].value,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?));
                // WRITE side of the enum-payload provenance diagnostic
                // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                // `EnumName.Variant(args)` construction path.
                crate::interpreter::note_enum_payload_function_opt(
                    "variant-construction", &("Result".to_string()), &(method_name.clone()), &payload,
                );
                return Ok(Value::Enum {
                    enum_name: "Result".to_string(),
                    variant: method_name.clone(),
                    payload,
                });
            }

            // Handle ClassName.new() - deprecated, delegate to ClassName() constructor with warning
            if method_name == "new" {
                eprintln!(
                    "\x1b[33mwarning\x1b[0m: {}.new() is deprecated, use {}() instead",
                    type_name, type_name
                );
                // Special builtin types
                match type_name.as_str() {
                    // Bug #185: "Map"/"Dict" fell through to the generic
                    // unknown-type fallback below, which stamps a phantom
                    // `__type__` string field onto the result — so
                    // `Map.new()`/`Dict.new()` returned a dict pre-loaded with
                    // one bogus entry instead of a genuinely empty one. Join
                    // them into the same empty-`Value::Dict` arm as
                    // `HashMap`/`BTreeMap`.
                    "HashMap" | "BTreeMap" | "Map" | "Dict" => {
                        return Ok(Value::Dict(std::sync::Arc::new(std::collections::HashMap::new())))
                    }
                    "HashSet" | "BTreeSet" => return Ok(Value::array(Vec::new())),
                    "Device" => {
                        return Ok(Value::Enum {
                            enum_name: "Device".to_string(),
                            variant: "CPU".to_string(),
                            payload: None,
                        })
                    }
                    _ => {
                        // Delegate to regular constructor ClassName(args...)
                        if classes.contains_key(type_name) {
                            return core::instantiate_class(
                                type_name,
                                args,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            );
                        }
                        // Fallback for unknown types: return typed dict
                        let mut fields = std::collections::HashMap::new();
                        fields.insert("__type__".to_string(), Value::text(type_name.to_string()));
                        for arg in args {
                            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                            if let Some(name) = &arg.name {
                                fields.insert(name.clone(), val);
                            }
                        }
                        return Ok(Value::Dict(std::sync::Arc::new(fields)));
                    }
                }
            }
        }
        // Try static method dispatch for ClassName.method() calls
        if segments.len() == 2 {
            let type_name = &segments[0];
            let method_name = &segments[1];

            // Check class methods for static methods
            if let Some(class_def) = classes.get(type_name.as_str()).cloned() {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(method) =
                    select_named_static_overload(class_def.methods.iter(), method_name, &evaluated_args)
                {
                    return core::exec_function_with_values(
                        &method,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
            }

            // Check impl_methods for static methods (local first, then GLOBAL_IMPL_METHODS fallback)
            let path_static_impl_methods = impl_methods
                .get(type_name.as_str())
                .cloned()
                .or_else(|| GLOBAL_IMPL_METHODS.with(|cell| cell.borrow().get(type_name.as_str()).cloned()));
            if let Some(methods) = path_static_impl_methods {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(method) = select_named_static_overload(methods.iter(), method_name, &evaluated_args) {
                    return core::exec_function_with_values(
                        &method,
                        &evaluated_args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
            }

            // Try as enum variant constructor (for user-defined enums + GLOBAL_ENUMS fallback)
            let tail_enum_def = enums
                .get(type_name.as_str())
                .cloned()
                .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(type_name.as_str()).cloned()));
            if let Some(enum_def) = tail_enum_def.as_ref() {
                if enum_def.variants.iter().any(|v| v.name == *method_name) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        Some(Box::new(evaluate_expr(
                            &args[0].value,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?))
                    } else {
                        let vals: Result<Vec<Value>, _> = args
                            .iter()
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .collect();
                        Some(Box::new(Value::Tuple(vals?)))
                    };
                    // WRITE side of the enum-payload provenance diagnostic
                    // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the generic
                    // `EnumName.Variant(args)` construction path.
                    crate::interpreter::note_enum_payload_function_opt(
                        "variant-construction", &(type_name.clone()), &(method_name.clone()), &payload,
                    );
                    return Ok(Value::Enum {
                        enum_name: type_name.clone(),
                        variant: method_name.clone(),
                        payload,
                    });
                }
            }

            // Cross-module fallback: search MODULE_CLASSES_CACHE for the class definition.
            // When a class is imported from another module, its ClassDef may not be in the
            // local `classes` map if the import path didn't fully merge definitions.
            // Search all cached module definitions for the class and dispatch the method.
            let cached_class_def: Option<Arc<ClassDef>> = MODULE_CLASSES_CACHE.with(|cache| {
                let cache = cache.borrow();
                for (_path, module_classes) in cache.iter() {
                    if let Some(class_def) = module_classes.get(type_name.as_str()) {
                        return Some(class_def.clone());
                    }
                }
                None
            });
            if let Some(class_def) = cached_class_def {
                // Also insert into local classes map so subsequent lookups are fast
                classes.insert(type_name.clone(), class_def.clone());

                // Try any method (static or instance-as-static)
                if let Some(method) = class_def.methods.iter().find(|m| m.name == *method_name) {
                    let is_new_method = method_name == "new";
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(type_name.to_string()));
                    }
                    let result = core::exec_function(method, args, env, functions, classes, enums, impl_methods, None);
                    if is_new_method {
                        core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(type_name));
                    }
                    return result;
                }
            }

            // Last resort: try GLOBAL_IMPL_METHODS for impl methods that weren't
            // merged into the class definition
            let global_path_impl_method: Option<Arc<FunctionDef>> = GLOBAL_IMPL_METHODS.with(|cell| {
                cell.borrow()
                    .get(type_name.as_str())
                    .and_then(|methods| methods.iter().find(|m| m.name == *method_name).cloned())
            });
            if let Some(func) = global_path_impl_method {
                let is_new_method = method_name == "new";
                if is_new_method {
                    core::IN_NEW_METHOD.with(|set| set.borrow_mut().insert(type_name.to_string()));
                }
                let result = core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                if is_new_method {
                    core::IN_NEW_METHOD.with(|set| set.borrow_mut().remove(type_name));
                }
                return result;
            }

            // Try the mangled free function name as a final fallback
            let mangled_path_name = format!("{}__{}", type_name, method_name);
            if let Some(func) = functions.get(&mangled_path_name).cloned() {
                return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            }

            // Builtin text static methods
            if type_name == "text" && method_name == "from_char_code" {
                let evaluated_args: Vec<Value> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect::<Result<Vec<_>, _>>()?;
                let code = match evaluated_args.first() {
                    Some(Value::Int(i)) => *i,
                    _ => 0,
                };
                let ch = char::from_u32(code as u32).unwrap_or('\0');
                return Ok(Value::text(ch.to_string()));
            }

            // Fallback: if segments[0] is bound as a value (e.g. a module-level
            // `var POS_AGENTS: [...] = ...`), the parser produces a Path expression
            // because the identifier is uppercase, even though the user wrote
            // `POS_AGENTS.len()` (an instance method call). Reconstruct as a
            // MethodCall and dispatch through the value-receiver path so builtins
            // like .len(), .push(), etc. work on module-level vars.
            let is_value = env.get(type_name).is_some()
                || crate::interpreter::MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(type_name));
            if is_value {
                let receiver = Box::new(Expr::Identifier(type_name.clone()));
                return crate::interpreter::interpreter_method::evaluate_method_call(
                    &receiver,
                    method_name,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                );
            }
        }

        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help("path calls must be Type::method() or Type::Variant()");
        return Err(CompileError::semantic_with_context(
            format!("unsupported path call: {:?}", segments),
            ctx,
        ));
    }

    // Handle generic type constructors like Channel[int]() and sizeof<T>()
    if let Expr::Index { receiver, index } = callee.as_ref() {
        if let Expr::Identifier(name) = receiver.as_ref() {
            // sizeof<T>() / size_of<T>() — returns byte size of type T
            if name == "sizeof" || name == "size_of" {
                let type_name = match index.as_ref() {
                    Expr::Identifier(t) => t.as_str(),
                    _ => "unknown",
                };
                let size: i64 = match type_name {
                    "f32" => 4,
                    "i32" | "u32" => 4,
                    "f64" => 8,
                    "i64" | "u64" => 8,
                    "i16" | "u16" => 2,
                    "i8" | "u8" | "bool" => 1,
                    "i128" | "u128" => 16,
                    _ => 8, // default pointer/word size
                };
                return Ok(Value::Int(size));
            }
            if name == BUILTIN_CHANNEL {
                let buffer_size = args.iter().find_map(|arg| {
                    if arg.name.as_deref() == Some("buffer") {
                        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                            .ok()
                            .and_then(|v| v.as_int().ok())
                            .map(|n| n as usize)
                    } else {
                        None
                    }
                });

                let channel = if let Some(size) = buffer_size {
                    ChannelValue::with_buffer(size)
                } else {
                    ChannelValue::new()
                };
                return Ok(Value::Channel(channel));
            }
        }
    }

    // Evaluate callee and dispatch based on value type
    let callee_val = evaluate_expr(callee, env, functions, classes, enums, impl_methods)?;
    match callee_val {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut captured_clone = Env::clone(&captured);
            core::exec_lambda(
                &params,
                &body,
                args,
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::BlockClosure { nodes, env: captured } => {
            let captured_clone = Env::clone(&captured);
            block_execution::exec_block_closure(&nodes, &captured_clone, functions, classes, enums, impl_methods)
        }
        Value::Function { def, captured_env, .. } => {
            let mut captured_env_clone = Env::clone(&captured_env);
            core::exec_function_with_captured_env(
                &def,
                args,
                env,
                &mut captured_env_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::NativeFunction(native) => {
            let evaluated: Vec<Value> = args
                .iter()
                .map(|a| {
                    if a.name.is_some() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("native functions do not support named arguments");
                        return Err(CompileError::semantic_with_context(
                            "native function does not support named arguments".to_string(),
                            ctx,
                        ));
                    }
                    evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)
                })
                .collect::<Result<Vec<_>, _>>()?;
            (native.func)(&evaluated)
        }
        Value::Constructor { class_name } => {
            core::instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods)
        }
        Value::EnumVariantConstructor {
            enum_name,
            variant_name,
        } => {
            // Construct enum variant with payload
            // Currently supports single payload value
            let payload = if args.is_empty() {
                None
            } else if args.len() == 1 {
                let val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                Some(Box::new(val))
            } else {
                // Multiple args - wrap in tuple
                let vals: Result<Vec<Value>, _> = args
                    .iter()
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .collect();
                Some(Box::new(Value::Tuple(vals?)))
            };
            Ok(Value::Enum {
                enum_name,
                variant: variant_name,
                payload,
            })
        }
        Value::Object { ref class, ref fields } => {
            // Support __call__ protocol: objects with __call__ method are callable
            let evaluated_args: Vec<Value> = args
                .iter()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(result) = super::interpreter_control::call_method_if_exists(
                &callee_val,
                "__call__",
                &evaluated_args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                Ok(result)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::NOT_CALLABLE)
                    .with_help(format!("type '{}' does not implement __call__", class));
                Err(CompileError::semantic_with_context(
                    format!("object of type '{}' is not callable", class),
                    ctx,
                ))
            }
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::NOT_CALLABLE)
                .with_help("value must be a function, lambda, constructor, or other callable type");
            Err(CompileError::semantic_with_context(
                "value is not callable".to_string(),
                ctx,
            ))
        }
    }
}

#[cfg(test)]
mod deprecated_new_dispatch_tests {
    use super::*;

    /// Bug #185: the deprecated `ClassName.new()` dispatch's builtin-type match
    /// special-cased only `"HashMap" | "BTreeMap"` to return a genuinely empty
    /// `Value::Dict`. `"Map"`/`"Dict"` (not registered in `classes`) fell
    /// through to the generic unknown-type fallback, which stamps a phantom
    /// `__type__` string field onto the result — so `Map.new()`/`Dict.new()`
    /// returned a dict pre-loaded with one bogus entry instead of an empty one.
    /// This broke native-build whenever compiler frontend `.spl` files used
    /// `Map.new()` (interpreted live by the seed).
    #[test]
    fn dict_new_returns_genuinely_empty_dict() {
        let callee: Box<Expr> = Box::new(Expr::Path(vec!["Dict".to_string(), "new".to_string()]));
        let mut env = Env::new();
        let result = evaluate_call(
            &callee,
            &[],
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("evaluate_call Dict.new()");
        match result {
            Value::Dict(map) => assert_eq!(map.len(), 0, "Dict.new() must not contain a phantom __type__ entry"),
            other => panic!("Dict.new() must return a Value::Dict, got {:?}", other),
        }
    }

    #[test]
    fn map_new_returns_genuinely_empty_dict() {
        let callee: Box<Expr> = Box::new(Expr::Path(vec!["Map".to_string(), "new".to_string()]));
        let mut env = Env::new();
        let result = evaluate_call(
            &callee,
            &[],
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("evaluate_call Map.new()");
        match result {
            Value::Dict(map) => assert_eq!(map.len(), 0, "Map.new() must not contain a phantom __type__ entry"),
            other => panic!("Map.new() must return a Value::Dict, got {:?}", other),
        }
    }
}
