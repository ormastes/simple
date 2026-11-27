//! Runtime application of user-defined function decorators.
//!
//! `@dec fn f(x): ...` must behave as if `f` is rebound to `dec(f_original)`,
//! and `@dec(a) fn f(...)` as `dec(a)(f_original)`. Before this module existed
//! the module-level interpreter path built the decorated value but stored it in
//! `env` only, where `evaluate_call`'s Priority-5 `functions` lookup
//! (`interpreter_call/mod.rs:569`) shadowed it, and the block-level paths
//! (nested `fn` inside `it`/closures) never applied decorators at all — so
//! `test/feature/usage/decorators_spec.spl` reported `add_one(5) == 6`
//! instead of 12.
//!
//! Compiler-directive and metadata decorators (`@inline`, `@deprecated`,
//! `@simd`, `@test`, ...) must keep their metadata-only behaviour. Effect
//! decorators (`@pure`/`@io`/...) never reach here: the parser diverts them
//! into `FunctionDef::effects` (`parser_impl/functions.rs:598`), so they are
//! not present in `FunctionDef::decorators`.

use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef};

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};

type Functions = HashMap<String, Arc<FunctionDef>>;
type Classes = HashMap<String, Arc<ClassDef>>;
type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

/// Decorator names that are compiler directives / metadata annotations and are
/// never evaluated as runtime wrapper functions.
///
/// Single source of truth: both the module-level and the block-level
/// interpreter paths consult this list. Hand-copying it is what produced the
/// `@noalloc` (2026-08-08) and `@always_inline` (2026-08-26) incidents.
pub fn is_directive_decorator(name: &str) -> bool {
    matches!(
        name,
        // Codegen / compile-time directives.
        "extern"
            | "deprecated"
            // GPU backend directives.
            | "gpu"
            | "gpu_kernel"
            | "gpu_device"
            | "gpu_shared"
            // VHDL backend directives (consumed by parse_vhdl_hardware_attrs).
            | "hardware"
            | "clocked"
            | "generic"
            | "flatten_struct_output"
            // A5 representation boundary manifest metadata.
            | "representation_boundary"
            // Allocation / mangling directives.
            | "noalloc"
            | "alloc"
            | "no_alloc"
            | "no_mangle"
            // Inlining hints — honoured by the LLVM backend
            // (codegen/llvm/backend_core.rs:134), no interpreter semantics.
            | "inline"
            | "always_inline"
            | "force_inline"
            // Memory-order directives (asm_embedded_hal_and_dual_run.md A.2).
            | "volatile"
            | "no_reorder"
            // Vectorisation and test-harness metadata. These are read by the
            // test runner / codegen as attributes and must never be called.
            | "simd"
            | "test"
            | "property_test"
            | "snapshot_test"
            | "bench"
            | "ignore"
            | "cfg"
    )
}

/// Opt-in strictness knob: `SIMPLE_STRICT_DECORATORS=1` turns the
/// unknown-module-level-decorator warning back into the hard error from
/// `unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08.md`.
/// Follows the `SIMPLE_JIT_STRICT` env-knob pattern
/// (`codegen/jit.rs`): any value other than `0` enables it. Read fresh on
/// each unknown decorator so tests observe changes without a rebuild.
fn strict_decorators_enabled() -> bool {
    std::env::var_os("SIMPLE_STRICT_DECORATORS").is_some_and(|value| value != "0")
}

/// Env key under which a decorator-rebound function is recorded.
///
/// `evaluate_call` resolves the `functions` map (Priority 5) before `env`
/// (Priority 6), so a decorated closure stored under its plain name is
/// shadowed by the original definition. Removing the `functions` entry instead
/// is not an option: the ORIGINAL body still resolves its own name through
/// that map when it recurses, and dropping it turned
/// `@double_result fn fact(n): ... fact(n - 1)` into "function `fact` not
/// found". So the binding is recorded under this sentinel prefix as well, and
/// `evaluate_call` probes it just before Priority 5. The sentinel lives in the
/// same `Env` as the binding, so it is scoped exactly like it -- no global
/// state and no cross-scope collisions. Recursion inside the original body
/// sees only that body's captured env, which has no sentinel, and therefore
/// keeps calling the undecorated original; that terminates, where routing it
/// back through the wrapper would be one more redundant wrap per level.
pub const DECORATED_FN_PREFIX: &str = "__decorated_fn__";

/// The env key recording that `name` has been rebound by a runtime decorator.
pub fn decorated_fn_key(name: &str) -> String {
    format!("{}{}", DECORATED_FN_PREFIX, name)
}

/// Set the first time a runtime decorator rebinds a function (every writer
/// of a `decorated_fn_key` sentinel sets it). `evaluate_call`'s Priority 4.5
/// used to build the sentinel key (a `format!` String) and run the full env
/// lookup cascade on EVERY identifier call to find out that no decorator
/// exists: measured 502 ns per call on a program with none (2026-11-07,
/// `SIMPLE_PERF_COUNTERS=1` EVALCALL_NS_P45_DECORATED). Process-global, not
/// thread-local: an Env carrying a sentinel can be called into from a
/// spawned thread, and a per-thread flag would make that call skip the
/// wrapper. Once set it stays set; it only says "worth looking", never
/// "bound here", so a false positive costs exactly the old lookup.
static DECORATED_FN_BOUND: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Record that a decorated function has been bound somewhere in this process.
pub fn mark_decorated_fn_bound() {
    DECORATED_FN_BOUND.store(true, std::sync::atomic::Ordering::Release);
}

/// Has any runtime decorator ever bound a function in this process?
pub fn any_decorated_fn_bound() -> bool {
    DECORATED_FN_BOUND.load(std::sync::atomic::Ordering::Acquire)
}

/// Apply the runtime (wrapper) decorators of `f` to `base`.
///
/// Returns `Ok(None)` when `f` carries no runtime decorator, in which case the
/// caller must keep its existing undecorated binding.
///
/// `strict` selects the behaviour for a decorator identifier that does not
/// resolve in scope. The module-level path passes `true` and reports the
/// decorator-specific diagnostic from
/// `unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08.md`
/// -- as a WARNING that skips the decorator (metadata, no semantic effect),
/// matching the lint's unknown-decorator diagnostic; setting
/// `SIMPLE_STRICT_DECORATORS=1` restores the hard error from that bug doc.
/// Block-level callers pass `false`: a nested `fn` may carry any project- or
/// tool-specific annotation, and treating an unresolvable one as metadata
/// preserves the pre-existing behaviour exactly.
pub fn apply_runtime_decorators(
    f: &FunctionDef,
    base: Value,
    strict: bool,
    env: &mut Env,
    functions: &mut Functions,
    classes: &mut Classes,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if f.decorators.is_empty() {
        return Ok(None);
    }

    let mut decorated = base;
    let mut applied = false;

    // Bottom-to-top: the decorator nearest the `fn` wraps first.
    for decorator in f.decorators.iter().rev() {
        if let Expr::Identifier(name) = &decorator.name {
            if is_directive_decorator(name) {
                continue;
            }
        }

        let decorator_fn = match crate::interpreter::evaluate_expr(
            &decorator.name,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ) {
            Ok(value) => value,
            Err(e) => {
                if !strict {
                    // Unknown annotation on a nested function: metadata, as before.
                    continue;
                }
                if let Expr::Identifier(name) = &decorator.name {
                    if !strict_decorators_enabled() {
                        // Unknown module-level decorator: warn once per
                        // occurrence and skip it (metadata, no semantic
                        // effect), matching the lint's unknown-decorator
                        // diagnostic. SIMPLE_STRICT_DECORATORS=1 restores the
                        // hard error below.
                        eprintln!(
                            "warning: unknown decorator `@{}` on function `{}` -- treating it as metadata with no semantic effect (set SIMPLE_STRICT_DECORATORS=1 to make this an error)",
                            name, f.name
                        );
                        continue;
                    }
                    return Err(CompileError::semantic_with_context(
                        format!("unknown decorator `@{}` on function `{}`", name, f.name),
                        ErrorContext::new()
                            .with_span(decorator.span)
                            .with_code(codes::UNDEFINED_VARIABLE)
                            .with_help(format!(
                                "`{}` is not a recognised compiler annotation and no function named `{}` is in scope to use as a runtime decorator -- fix the typo, register `{}` as a compiler annotation, or define a `fn {}(f)` runtime decorator",
                                name, name, name, name
                            )),
                    ));
                }
                return Err(e);
            }
        };

        // A name that resolves but is not callable is an annotation that merely
        // collides with an in-scope binding, not a decorator. `@logged fn f()`
        // beside `var logged = false` (test/feature/usage/aop_spec.spl's
        // `attr(logged)` pointcut) resolved the bool and then died with
        // "cannot call value of type bool". Block-level callers already treat an
        // UNRESOLVABLE annotation as metadata (`strict == false`, see the
        // doc comment above); a resolvable-but-not-callable one is the same
        // situation and gets the same treatment. Strict (module-level) callers
        // keep reporting it, since there the collision is with a module global
        // and is much more likely to be a real mistake.
        if !strict && !is_callable(&decorator_fn) {
            continue;
        }

        // `@dec(args)` — call the factory first to obtain the real decorator.
        let actual_decorator = if let Some(args) = &decorator.args {
            let mut arg_values = Vec::with_capacity(args.len());
            for arg in args {
                arg_values.push(crate::interpreter::evaluate_expr(
                    &arg.value,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?);
            }
            crate::interpreter::call_value_with_args(
                &decorator_fn,
                arg_values,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
        } else {
            decorator_fn
        };

        decorated = crate::interpreter::call_value_with_args(
            &actual_decorator,
            vec![decorated],
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?;
        applied = true;
    }

    Ok(if applied { Some(decorated) } else { None })
}

/// Whether `value` can be applied as a runtime decorator.
///
/// Mirrors the arms `crate::interpreter::call_value_with_args`
/// (`interpreter_eval.rs:168`) actually accepts: lambdas, functions, native
/// functions, and objects implementing the `__call__` protocol.
fn is_callable(value: &Value) -> bool {
    matches!(
        value,
        Value::Lambda { .. } | Value::Function { .. } | Value::NativeFunction(_) | Value::Object { .. }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::Node;

    /// Serializes the two `SIMPLE_STRICT_DECORATORS` tests: the knob is a
    /// process-global env var and `cargo test` runs tests on parallel threads.
    static STRICT_DECORATORS_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn parse_single_function(source: &str) -> FunctionDef {
        let module = simple_parser::Parser::new(source).parse().expect("source must parse");
        module
            .items
            .into_iter()
            .find_map(|item| match item {
                Node::Function(f) => Some(f),
                _ => None,
            })
            .expect("source must define one function")
    }

    fn apply_at_module_level(f: &FunctionDef) -> Result<Option<Value>, CompileError> {
        let base = Value::Function {
            name: f.name.clone(),
            def: Arc::new(f.clone()),
            captured_env: Arc::new(Env::new()),
        };
        let mut env = Env::new();
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let enums = HashMap::new();
        let impl_methods = HashMap::new();
        apply_runtime_decorators(f, base, true, &mut env, &mut functions, &mut classes, &enums, &impl_methods)
    }

    #[test]
    fn representation_boundary_is_directive_decorator() {
        assert!(is_directive_decorator("representation_boundary"));
    }

    #[test]
    fn unknown_module_level_decorator_warns_and_is_skipped_by_default() {
        let _guard = STRICT_DECORATORS_ENV_LOCK.lock().unwrap();
        std::env::remove_var("SIMPLE_STRICT_DECORATORS");
        let f = parse_single_function("@totally_unknown_tag\nfn foo() -> i64:\n    1\n");
        let result = apply_at_module_level(&f);
        let decorated = result.expect("unknown decorator must not be a hard error by default");
        assert!(decorated.is_none(), "an unknown decorator has no semantic effect");
    }

    #[test]
    fn unknown_module_level_decorator_is_hard_error_under_strict_knob() {
        let _guard = STRICT_DECORATORS_ENV_LOCK.lock().unwrap();
        std::env::set_var("SIMPLE_STRICT_DECORATORS", "1");
        let f = parse_single_function("@totally_unknown_tag\nfn foo() -> i64:\n    1\n");
        let result = apply_at_module_level(&f);
        std::env::remove_var("SIMPLE_STRICT_DECORATORS");
        let err = result.expect_err("SIMPLE_STRICT_DECORATORS=1 must restore the hard error");
        let message = format!("{err}");
        assert!(
            message.contains("unknown decorator `@totally_unknown_tag` on function `foo`"),
            "error must name the decorator and the function: {message}"
        );
    }

    #[test]
    fn known_directive_decorator_is_still_metadata_only() {
        let _guard = STRICT_DECORATORS_ENV_LOCK.lock().unwrap();
        std::env::remove_var("SIMPLE_STRICT_DECORATORS");
        let f = parse_single_function("@inline\nfn foo() -> i64:\n    1\n");
        let decorated = apply_at_module_level(&f).expect("a known directive decorator must apply cleanly");
        assert!(decorated.is_none(), "directive decorators stay metadata-only");
    }
}
