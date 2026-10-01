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

/// Apply the runtime (wrapper) decorators of `f` to `base`.
///
/// Returns `Ok(None)` when `f` carries no runtime decorator, in which case the
/// caller must keep its existing undecorated binding.
///
/// `strict` selects the behaviour for a decorator identifier that does not
/// resolve in scope. The module-level path passes `true` and reports the
/// decorator-specific diagnostic from
/// `unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08.md`.
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
