//! Runtime execution of `before` / `after_success` / `after_error` AOP advice
//! on the interpreter path.
//!
//! Before this module existed, `on pc{...} use advice before priority N` was
//! parsed into `Node::AopAdvice` and then DROPPED: the module-level statement
//! executor listed `Node::AopAdvice(_)` in its no-op arm
//! (`interpreter_eval.rs`), the block-level executor never looked at it at
//! all, and the only weaver in the tree (`crate::weaving`) operates on MIR and
//! has no caller outside its own unit tests. So every advice-execution
//! assertion in `test/feature/usage/aop_spec.spl` and
//! `test/feature/usage/aop_pointcut_spec.spl` observed `false`.
//!
//! Design: a thread-local registry plus call-site interception, NOT weaving.
//! `on ...` is an executable statement whose effect starts when it runs, and
//! a wildcard pointcut (`execution(* calc*(..))`) applies to several functions
//! that are not known at declaration time, so wrapping a single definition at
//! declaration time (the `crate::decorator_apply` strategy) cannot express it.
//!
//! Pointcut matching reuses `crate::predicate` — the same `Predicate`,
//! `Selector` and glob engine the DI/`AopConfig` path already uses. The parser
//! stores the whole `pc{...}` body verbatim as a single selector name
//! (`stmt_parsing/aop.rs::parse_predicate_from_string`), so the registry
//! re-parses that text with `crate::predicate_parser::parse_predicate`, which
//! implements the full `& | !` grammar.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{AopAdvice, AdviceType, ClassDef, Decorator, EnumDef, Expr, FunctionDef};

use crate::error::{codes, CompileError, ErrorContext};
use crate::predicate::{MatchContext, Predicate};
use crate::value::{Env, Value};

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

#[derive(Debug, Clone)]
struct AdviceRule {
    predicate: Predicate,
    advice: String,
    advice_type: AdviceType,
    priority: i64,
    order: usize,
}

thread_local! {
    static ADVICE: RefCell<Vec<AdviceRule>> = const { RefCell::new(Vec::new()) };
    /// Re-entrancy guard. A pointcut such as `execution(* *(..))` matches the
    /// advice function itself; without this, running the advice would match
    /// again and recurse forever.
    static IN_ADVICE: RefCell<bool> = const { RefCell::new(false) };
}

/// Register an `on pc{...} use <advice> <kind> priority <n>` declaration.
///
/// The advice name is resolved eagerly against `functions` so a typo is a hard
/// error HERE, at the declaration. That is what lets the join point treat a
/// later "advice not found" as an out-of-scope rule and skip it (see
/// `run_kind`) instead of failing the call.
pub(crate) fn register_advice(
    decl: &AopAdvice,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Result<(), CompileError> {
    if !functions.contains_key(&decl.interceptor) {
        return Err(CompileError::semantic_with_context(
            format!("advice function `{}` not found", decl.interceptor),
            ErrorContext::new()
                .with_span(decl.span)
                .with_code(codes::UNDEFINED_FUNCTION)
                .with_help("define the advice function before the `on pc{...} use ...` declaration"),
        ));
    }
    let text = pointcut_text(decl);
    let predicate = crate::predicate_parser::parse_predicate(&text).map_err(|e| {
        CompileError::semantic_with_context(
            format!("invalid pointcut `pc{{{}}}`: {}", text, e),
            ErrorContext::new()
                .with_span(decl.span)
                .with_code(codes::INVALID_POINTCUT_SELECTOR)
                .with_help("supported selectors here are execution(...), attr(...), within(...) combined with & | !"),
        )
    })?;
    ADVICE.with(|cell| {
        let mut rules = cell.borrow_mut();
        let order = rules.len();
        rules.push(AdviceRule {
            predicate,
            advice: decl.interceptor.clone(),
            advice_type: decl.advice_type,
            priority: decl.priority.unwrap_or(0),
            order,
        });
    });
    Ok(())
}

/// Recover the raw `pc{...}` body. The parser keeps it verbatim in the
/// selector name with no args; the `Not`/`And`/`Or` arms are handled for
/// robustness should the parser ever build a real tree.
fn pointcut_text(decl: &AopAdvice) -> String {
    use simple_parser::ast::PredicateKind;
    fn render(kind: &PredicateKind) -> String {
        match kind {
            PredicateKind::Selector { name, args } => {
                if args.is_empty() {
                    name.clone()
                } else {
                    format!("{}({})", name, args.join(", "))
                }
            }
            PredicateKind::Not(inner) => format!("!({})", render(&inner.kind)),
            PredicateKind::And(a, b) => format!("({}) & ({})", render(&a.kind), render(&b.kind)),
            PredicateKind::Or(a, b) => format!("({}) | ({})", render(&a.kind), render(&b.kind)),
        }
    }
    render(&decl.pointcut.kind)
}

/// True when at least one advice is registered. Kept cheap so the hot call
/// path pays nothing when AOP is unused ("zero overhead when AOP is not
/// enabled", aop_spec.spl Behaviors).
pub(crate) fn has_advice() -> bool {
    ADVICE.with(|cell| !cell.borrow().is_empty())
}

fn decorator_name(d: &Decorator) -> Option<String> {
    match &d.name {
        Expr::Identifier(name) => Some(name.clone()),
        _ => None,
    }
}

/// Attribute names visible to `attr(...)`. `@logged` on a nested `fn` survives
/// as a non-directive decorator (see `crate::decorator_apply`), and `#[...]`
/// attributes land in `FunctionDef::attributes`; both are user-visible
/// annotations, so both feed the selector.
fn function_attrs(func: &FunctionDef) -> Vec<String> {
    let mut attrs: Vec<String> = func.decorators.iter().filter_map(decorator_name).collect();
    attrs.extend(func.attributes.iter().map(|a| a.name.clone()));
    attrs
}

/// `* name(Any, Any)` — the same shape `weaving::matcher::build_signature`
/// produces, so one pointcut text means the same thing on both paths.
fn function_signature(func: &FunctionDef) -> String {
    let params = func
        .params
        .iter()
        .map(|_| "Any".to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!("* {}({})", func.name, params)
}

/// Advice names matching `func`, highest priority first. `before` runs
/// highest-priority-first; `after_*` runs highest-priority-LAST (aop_spec.spl
/// Behaviors), so the caller reverses for the after kinds.
fn matching_advice(func: &FunctionDef, kind: AdviceType) -> Vec<String> {
    let signature = function_signature(func);
    let attrs = function_attrs(func);
    let ctx = MatchContext::new()
        .with_type_name(&func.name)
        .with_module_path(&func.name)
        .with_attrs(&attrs)
        .with_signature(&signature);
    ADVICE.with(|cell| {
        let rules = cell.borrow();
        let mut matched: Vec<&AdviceRule> = rules
            .iter()
            .filter(|r| r.advice_type == kind && r.advice != func.name && r.predicate.matches(&ctx))
            .collect();
        matched.sort_by(|a, b| b.priority.cmp(&a.priority).then_with(|| a.order.cmp(&b.order)));
        matched.into_iter().map(|r| r.advice.clone()).collect()
    })
}

fn is_err_result(value: &Value) -> bool {
    matches!(value, Value::Enum { enum_name, variant, .. } if &**enum_name == "Result" && &**variant == "Err")
}

/// Run every `before` advice matching `func`.
pub(crate) fn run_before(
    func: &FunctionDef,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(), CompileError> {
    run_kind(
        AdviceType::Before,
        false,
        func,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )
}

/// Run `after_success` or `after_error` advice, chosen by the target's result.
pub(crate) fn run_after(
    func: &FunctionDef,
    result: &Value,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(), CompileError> {
    let kind = if is_err_result(result) {
        AdviceType::AfterError
    } else {
        AdviceType::AfterSuccess
    };
    run_kind(kind, true, func, env, functions, classes, enums, impl_methods)
}

#[allow(clippy::too_many_arguments)] // reason: mirrors the interpreter's function-execution entrypoints
fn run_kind(
    kind: AdviceType,
    reverse: bool,
    func: &FunctionDef,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(), CompileError> {
    if IN_ADVICE.with(|c| *c.borrow()) {
        return Ok(());
    }
    let mut names = matching_advice(func, kind);
    if names.is_empty() {
        return Ok(());
    }
    if reverse {
        names.reverse();
    }
    for name in names {
        // The rule outlived the scope its advice was declared in — the
        // registry is process-wide but `on ...` is a scoped statement, and a
        // nested advice function is gone once its block ends. `register_advice`
        // already rejected an undefined name, so this can only be an
        // out-of-scope rule: skip it rather than failing an unrelated call.
        let Some(advice_fn) = functions.get(&name).cloned() else {
            continue;
        };
        IN_ADVICE.with(|c| *c.borrow_mut() = true);
        let outcome = exec_advice_in_join_point_scope(&advice_fn, env, functions, classes, enums, impl_methods);
        IN_ADVICE.with(|c| *c.borrow_mut() = false);
        outcome?;
    }
    Ok(())
}

/// Execute a zero-argument advice body against the join point's scope and write
/// back the bindings it changed.
///
/// Advice observes and records state (`advice_called = true`, `count = count +
/// 1`), so it must see the scope its declaration sits in. A plain call cannot
/// deliver that: `exec_function_inner` builds the callee env from
/// `captured_env_with_live_globals(func, &Env::new())` — an EMPTY captured env
/// — so an assignment inside the callee lands on a local that
/// `sync_owned_captured_globals` then skips (`local_env.is_local(name)`), and
/// the caller never sees it. That gap is general to nested `fn`s and closures
/// and is NOT fixed here (see the PR notes); this function confines the
/// woven-in-place semantics to advice, where "the advice body runs at the join
/// point" is the specified behaviour.
///
/// Only names that ALREADY existed at the join point are copied back, so
/// advice-local variables do not leak into the caller.
fn exec_advice_in_join_point_scope(
    advice_fn: &FunctionDef,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(), CompileError> {
    let mut advice_env = env.clone();
    super::function_exec::execute_function_body(
        advice_fn,
        HashMap::new(),
        &mut advice_env,
        functions,
        classes,
        enums,
        impl_methods,
        false,
    )?;
    let names: Vec<String> = env.keys().cloned().collect();
    for name in names {
        if advice_fn.params.iter().any(|p| p.name == name) {
            continue;
        }
        if let Some(new_value) = advice_env.get(&name).cloned() {
            if env.get(&name) != Some(&new_value) {
                env.insert(name, new_value);
            }
        }
    }
    Ok(())
}

/// Lexical scope for advice declared inside a block.
///
/// `on pc{...}` is an executable statement, so a declaration inside an `it`
/// body (or any other block) must stop applying when that block ends — exactly
/// like the `CONST_NAMES` / `IMMUTABLE_VARS` save-and-restore the block
/// executor already does. Without this, `aop_pointcut_spec.spl` counted 7
/// invocations where 2 were expected: every earlier example's rule was still
/// live and its advice function name (`counter`, `marker`) was re-used by the
/// next example, so the stale rules resolved and fired again.
///
/// Registrations are append-only within a scope, so restoring is a truncate.
pub(crate) struct AdviceScope(usize);

impl AdviceScope {
    pub(crate) fn enter() -> Self {
        AdviceScope(ADVICE.with(|cell| cell.borrow().len()))
    }
}

impl Drop for AdviceScope {
    fn drop(&mut self) {
        ADVICE.with(|cell| cell.borrow_mut().truncate(self.0));
    }
}
