// Core function execution logic

use super::arg_binding::{bind_args, bind_args_with_values};
use super::async_support::{is_async_function, wrap_in_promise};
use super::macros::*;
use crate::error::CompileError;
use crate::interpreter::{
    exec_block_fn, Control, CONST_NAMES, IMMUTABLE_VARS, IN_IMMUTABLE_FN_METHOD, GENERATOR_YIELDS, CURRENT_EXEC_MODULE,
    FUNCTION_MODULE_OWNER, MODULE_ENV_BY_OWNER, MODULE_GLOBALS, owned_global, owned_globals_snapshot,
    owner_bindings, owner_has_globals, seed_owner_globals, set_owned_global, visit_pattern_binding_names,
};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{
    Argument, Attribute, Block, ClassDef, EnumDef, Expr, FunctionDef, LetStmt, Mutability, Node, Pattern, ReturnStmt,
    SelfMode, StorageClass, Type,
};
use simple_runtime::value::diagram_sffi;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::{Arc, LazyLock, Weak};
use std::time::Instant;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

/// Origin of the value presented to the SFFI v2 return-contract boundary.
/// Keeping this separate from `Value` prevents fallthrough from first being
/// laundered into `Value::Nil` (and then into `Option::None`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SffiReturnOrigin {
    ExplicitReturn,
    TailValue,
    UnitFallthrough,
    ExplicitOptionalNone,
    ForeignRawResult,
    MissingReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SffiReturnContract {
    Unit,
    Optional,
    NonOptional,
}

fn sffi_return_contract(return_type: Option<&Type>) -> SffiReturnContract {
    match return_type {
        None => SffiReturnContract::Unit,
        Some(Type::Tuple(elements)) if elements.is_empty() => SffiReturnContract::Unit,
        // All three void spellings must classify as Unit. `unit` and `void`
        // are the keyword forms; the compiler already maps all of
        // "void" | "unit" | "()" to TypeId::VOID (type_inference_config.rs,
        // hir/lower/type_resolver.rs). Missing them here made a bare
        // `return` in a `-> unit` fn yield Value::Nil under a NonOptional
        // contract, faulting with "nil is forbidden by the non-optional
        // return contract".
        Some(Type::Simple(name)) if name == "()" || name == "unit" || name == "void" => {
            SffiReturnContract::Unit
        }
        Some(Type::Optional(_)) => SffiReturnContract::Optional,
        // Explicit generic spelling `Option<T>` / `Optional<T>` is equivalent
        // to the `T?` sugar (which parses to `Type::Optional`) and must be
        // classified the same way, or `return nil` faults under the
        // non-optional contract for a semantically-optional return type.
        Some(Type::Generic { name, args }) if args.len() == 1 && (name == "Option" || name == "Optional") => {
            SffiReturnContract::Optional
        }
        Some(_) => SffiReturnContract::NonOptional,
    }
}

fn is_language_unit_return_type(return_type: Option<&Type>) -> bool {
    matches!(sffi_return_contract(return_type), SffiReturnContract::Unit)
}

pub(crate) fn validate_sffi_return_contract(
    function_name: &str,
    return_type: Option<&Type>,
    origin: SffiReturnOrigin,
    value: Option<Value>,
) -> Result<Value, CompileError> {
    let contract = sffi_return_contract(return_type);
    match (origin, contract, value) {
        (SffiReturnOrigin::UnitFallthrough, SffiReturnContract::Unit, None) => Ok(Value::Nil),
        (SffiReturnOrigin::MissingReturn, _, None) => {
            let ctx = crate::error::ErrorContext::new()
                .with_code(crate::error::codes::SFFI_MISSING_RETURN)
                .with_help("return a contract-valid value explicitly");
            Err(CompileError::semantic_with_context(
                format!("missing return in non-unit function '{function_name}'"),
                ctx,
            ))
        }
        (_, SffiReturnContract::NonOptional, Some(Value::Nil)) => {
            let ctx = crate::error::ErrorContext::new()
                .with_code(crate::error::codes::SFFI_NULL_FORBIDDEN)
                .with_help("return a non-nil value or declare an optional return type");
            Err(CompileError::semantic_with_context(
                format!("nil is forbidden by the non-optional return contract of '{function_name}'"),
                ctx,
            ))
        }
        (_, _, Some(value)) => {
            if let Some(Type::Simple(type_name)) = return_type {
                if is_unit_type(type_name) {
                    if let Err(error) = validate_unit_type(&value, type_name) {
                        let ctx = crate::error::ErrorContext::new()
                            .with_code(crate::error::codes::TYPE_MISMATCH)
                            .with_help("ensure the value matches the expected unit type");
                        return Err(CompileError::semantic_with_context(
                            format!("return type mismatch in '{function_name}': {error}"),
                            ctx,
                        ));
                    }
                }
            }
            Ok(value)
        }
        (_, _, None) => {
            let ctx = crate::error::ErrorContext::new()
                .with_code(crate::error::codes::SFFI_MISSING_RETURN)
                .with_help("return a contract-valid value explicitly");
            Err(CompileError::semantic_with_context(
                format!("missing return in non-unit function '{function_name}'"),
                ctx,
            ))
        }
    }
}

fn function_module_owner(func: &FunctionDef) -> Option<Arc<str>> {
    let key = func as *const FunctionDef as usize;
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

// Per-call environment setup is O(args), not O(globals): the callee frame gets
// a `GlobalScope` — four `Arc` handles to the owner's static module env, its
// import table and the live per-owner global stores — and resolves every
// global through that parent pointer. Nothing is materialized, so there is no
// template to cache and no generation to invalidate. The previous design
// (cached per-owner env template + write-log patching, 2026-08-21) still
// cloned a growing overlay per call and rescanned every binding per changed
// global; measured at 2.1 GB RSS and >150 s on `lint driver_types.spl`.
// doc/08_tracking/bug/seed_interpreter_env_rebuild_per_call_o_globals_2026-08-21.md

/// The module scope for functions owned by `owner`, over the CURRENT live
/// stores. Seeds the owner's live store from its module-load values on first
/// use, as the materializing path did.
pub(crate) fn owner_scope(owner: &Arc<str>) -> GlobalScope {
    seed_owner_globals(owner);
    let module_env = MODULE_ENV_BY_OWNER.with(|cell| cell.borrow().get(owner).cloned());
    GlobalScope::new(
        Arc::clone(owner),
        module_env,
        owner_bindings(owner),
        owned_globals_snapshot(),
    )
}

pub(crate) fn captured_env_with_live_globals(func: &FunctionDef, captured_env: &Env) -> Env {
    let Some(owner) = function_module_owner(func) else {
        let mut initial_env = captured_env.clone();
        let live_globals = MODULE_GLOBALS.with(|cell| {
            let globals = cell.borrow();
            captured_env
                .keys()
                .filter_map(|name| {
                    if captured_env.is_local(name) {
                        return None;
                    }
                    globals.get(name).map(|value| (name.clone(), value.clone()))
                })
                .collect::<Vec<_>>()
        });
        initial_env.extend(live_globals);
        return initial_env;
    };
    // The captured env's own entries (a closure's captured locals) stay in the
    // overlay and shadow the scope, exactly as they shadowed the materialized
    // base before; the owner's live globals and imports sit above any base
    // the captured env carried, and the static module env below it.
    let mut env = captured_env.clone();
    env.clear_dirty();
    env.set_scope(owner_scope(&owner));
    env
}

/// Call-entry publish for a frame about to call out: drop the frame's store
/// snapshot FIRST so the publish writes into uniquely-owned maps (no
/// `Arc::make_mut` copy of the owner's whole global map), then re-point so
/// default-argument evaluation in this frame still sees live globals.
pub(crate) fn publish_and_repoint(env: &mut Env) {
    env.release_scope();
    publish_live_bound_globals(env);
    env.refresh_scope(owned_globals_snapshot());
}

pub(crate) fn publish_live_bound_globals(env: &Env) {
    let changed = env
        .overlay_entries()
        .filter(|(name, _)| !env.is_local(name) && !env.is_refreshed_global(name))
        .filter_map(|(name, value)| {
            env.global_binding(name)
                .map(|(owner, source_name)| (owner, source_name, value.clone()))
        })
        .collect::<Vec<_>>();
    if changed.is_empty() {
        return;
    }
    for (owner, name, value) in &changed {
        set_owned_global(owner, name, value.clone(), false);
    }
    MODULE_GLOBALS.with(|cell| {
        let mut globals = cell.borrow_mut();
        for (_, name, value) in changed {
            globals.insert(name, value);
        }
    });
}

/// Make a frame see the current live globals: O(1) scope re-point, plus a
/// refresh of any stale global copy sitting in the frame's own overlay.
pub(crate) fn refresh_live_bound_globals(env: &mut Env) {
    env.refresh_scope(owned_globals_snapshot());
    let stale = env
        .overlay_entries()
        .filter(|(name, _)| !env.is_local(name))
        .filter_map(|(name, _)| env.global_binding(name))
        .collect::<HashSet<_>>();
    for (owner, name) in stale {
        if let Some(value) = owned_global(&owner, &name) {
            env.refresh_bound_global(&owner, &name, value);
        }
    }
}

pub(crate) fn sync_live_bound_globals(local_env: &Env, outer_env: &mut Env) {
    publish_live_bound_globals(local_env);
    outer_env.refresh_scope(owned_globals_snapshot());
    let mut packets = local_env
        .forwarded_globals()
        .map(|((owner, name), value)| ((Arc::clone(owner), name.clone()), value.clone()))
        .collect::<HashMap<_, _>>();
    for (local_name, _) in local_env.overlay_entries() {
        if local_env.is_local(local_name) {
            continue;
        }
        let Some((owner, source_name)) = local_env.global_binding(local_name) else {
            continue;
        };
        if let Some(value) = owned_global(&owner, &source_name) {
            packets.insert((owner, source_name), value);
        }
    }
    let caller_owner = CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    for ((owner, name), _) in packets {
        let Some(value) = owned_global(&owner, &name) else {
            continue;
        };
        let refreshed = outer_env.refresh_bound_global(&owner, &name, value.clone());
        if caller_owner.as_ref() != Some(&owner) || !refreshed {
            outer_env.forward_globals(owner, [(name, value)]);
        }
    }
}

/// The caller released its store snapshot for the callee's lifetime. It is
/// re-pointed here AFTER the store writes below — never before: a snapshot
/// taken first would share the owner map with the store, and the write's
/// `Arc::make_mut` would then copy every global of that owner
/// (tests/interpreter_call_env_o_args.rs caught exactly that ordering).
pub(crate) fn sync_owned_captured_globals(func: &FunctionDef, local_env: &Env, outer_env: &mut Env) {
    let caller_owner = CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    let Some(owner) = function_module_owner(func).or_else(|| caller_owner.clone()) else {
        outer_env.refresh_scope(owned_globals_snapshot());
        return;
    };
    if !owner_has_globals(&owner) {
        outer_env.refresh_scope(owned_globals_snapshot());
        return;
    }
    let mut changed = Vec::new();
    let mut live_for_caller = Vec::new();
    for (local_name, value) in local_env.overlay_entries() {
        if func.params.iter().any(|param| param.name == *local_name) || local_env.is_local(local_name) {
            continue;
        }
        let (target_owner, target_name) = local_env
            .global_binding(local_name)
            .unwrap_or_else(|| (Arc::clone(&owner), local_name.clone()));
        let Some(current) = owned_global(&target_owner, &target_name) else {
            continue;
        };
        if local_env.is_refreshed_global(local_name) {
            live_for_caller.push((target_owner, target_name, current));
        } else {
            let entry = (target_owner, target_name, value.clone());
            changed.push(entry.clone());
            live_for_caller.push(entry);
        }
    }
    for (target_owner, target_name, value) in &changed {
        set_owned_global(target_owner, target_name, value.clone(), false);
    }
    // Mirror mutated owned globals into the shared flat MODULE_GLOBALS. Deferred
    // lazy imports keep each module's globals in MODULE_GLOBALS_BY_OWNER, but a
    // cross-module read of an *imported/exported* global (e.g. the AST arena
    // `expr_tag` defined in compiler.core.ast_expr and read from the desugar and
    // MIR modules) resolves a bare identifier through the flat MODULE_GLOBALS
    // fallback. That flat entry is only seeded with the owner's *initial* value
    // at module-load time, so subsequent growth of an exported array was invisible
    // across the module boundary and indexing it read length 0 -> "array index out
    // of bounds". Keeping the flat map in step with the owner map restores the
    // shared-global liveness the pre-defer flat model had, while per-owner reads
    // (env / MODULE_GLOBALS_BY_OWNER) still take precedence so same-named private
    // globals stay isolated.
    if !changed.is_empty() {
        MODULE_GLOBALS.with(|cell| {
            let mut globals = cell.borrow_mut();
            for (_, name, value) in &changed {
                globals.insert(name.clone(), value.clone());
            }
        });
    }
    // Store writes are done: now the caller may hold a snapshot again. It
    // reads every live global through the re-pointed scope; only stale copies
    // in its overlay still need the explicit refresh below.
    outer_env.refresh_scope(owned_globals_snapshot());
    let Some(caller_owner) = caller_owner else {
        return;
    };
    let mut forwarded = local_env
        .forwarded_globals()
        .map(|((owner, name), value)| ((Arc::clone(owner), name.clone()), value.clone()))
        .collect::<HashMap<_, _>>();
    for (target_owner, name, value) in live_for_caller {
        forwarded.insert((target_owner, name), value);
    }
    let mut refreshed = Vec::new();
    for ((entry_owner, name), fallback) in forwarded {
        let value = owned_global(&entry_owner, &name).unwrap_or(fallback);
        if entry_owner == caller_owner {
            if !outer_env.is_local(&name) {
                refreshed.push((name, value));
            } else {
                outer_env.forward_globals(entry_owner, [(name, value)]);
            }
        } else {
            outer_env.refresh_bound_global(&entry_owner, &name, value.clone());
            outer_env.forward_globals(entry_owner, [(name, value)]);
        }
    }
    let through_scope = outer_env.scope().is_some();
    let refreshed = refreshed
        .into_iter()
        .filter(|(name, _)| !through_scope || outer_env.has_overlay_entry(name))
        .collect::<Vec<_>>();
    outer_env.refresh_globals(refreshed);
}

fn mark_pattern_locals(pattern: &Pattern, env: &mut Env) {
    visit_pattern_binding_names(pattern, &mut |name| env.mark_local(name.to_owned()));
}

pub(super) fn mark_nodes_locals(nodes: &[Node], env: &mut Env) {
    for node in nodes {
        match node {
            Node::Let(stmt) => mark_pattern_locals(&stmt.pattern, env),
            Node::Const(stmt) => env.mark_local(stmt.name.clone()),
            Node::Static(stmt) => env.mark_local(stmt.name.clone()),
            Node::Function(def) => env.mark_local(def.name.clone()),
            Node::Struct(def) => env.mark_local(def.name.clone()),
            Node::Class(def) => env.mark_local(def.name.clone()),
            Node::Enum(def) => env.mark_local(def.name.clone()),
            Node::Newtype(def) => env.mark_local(def.name.clone()),
            _ => {}
        }
    }
}

fn mark_block_locals(block: &Block, env: &mut Env) {
    mark_nodes_locals(&block.statements, env);
}

static INTERPRETER_CALL_TRACE: LazyLock<Option<String>> =
    LazyLock::new(|| std::env::var("SIMPLE_INTERPRETER_CALL_TRACE").ok());

fn trace_interpreter_call_enter(func: &FunctionDef) -> Option<Instant> {
    let filter = INTERPRETER_CALL_TRACE.as_deref()?;
    if filter == "1" || filter == "all" || func.name.contains(filter) {
        if func.name == "empty" {
            let key = func as *const FunctionDef as usize;
            let owner = FUNCTION_MODULE_OWNER.with(|cell| cell.borrow().get(&key).cloned());
            let params = func
                .params
                .iter()
                .map(|param| param.name.as_str())
                .collect::<Vec<_>>()
                .join(",");
            eprintln!(
                "[interp-call] enter {} owner={} params=[{}] static={}",
                func.name,
                owner.as_deref().unwrap_or("<unknown>"),
                params,
                func.is_static
            );
        } else {
            eprintln!("[interp-call] enter {}", func.name);
        }
        Some(Instant::now())
    } else {
        None
    }
}

fn trace_interpreter_call_exit(start: Option<Instant>, name: &str, status: &str) {
    if let Some(start) = start {
        eprintln!(
            "[interp-call] exit {name} status={status} elapsed_ms={}",
            start.elapsed().as_millis()
        );
    }
}

fn is_driver_stub_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Call { callee, .. } => {
            if let Expr::Identifier(name) = callee.as_ref() {
                matches!(name.as_str(), "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo")
            } else {
                false
            }
        }
        Expr::Identifier(name) => matches!(name.as_str(), "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo"),
        _ => false,
    }
}

fn is_driver_stub_body(body: &Block) -> bool {
    match body.statements.as_slice() {
        [] => true,
        [Node::Pass(_)] => true,
        [Node::Expression(expr)] => is_driver_stub_expr(expr),
        _ => false,
    }
}

fn driver_manifest_attr(func: &FunctionDef) -> Option<&Attribute> {
    func.attributes
        .iter()
        .find(|attr| attr.name == "driver" || attr.name == "native_lib")
}

fn driver_attr_arg(func: &FunctionDef, key: &str, fallback_idx: usize) -> Option<Expr> {
    let attr = driver_manifest_attr(func)?;
    if let Some(named) = &attr.named_args {
        for (name, value) in named {
            if name == key {
                return Some(value.clone());
            }
        }
    }
    attr.args.as_ref()?.get(fallback_idx).cloned()
}

fn driver_ops_arg(func: &FunctionDef) -> Option<Expr> {
    let attr = driver_manifest_attr(func)?;
    let named = attr.named_args.as_ref()?;
    named
        .iter()
        .find_map(|(name, value)| if name == "ops" { Some(value.clone()) } else { None })
}

fn positional_arg(value: Expr, span: simple_parser::Span) -> Argument {
    Argument {
        name: None,
        value,
        span,
        label: None,
    }
}

fn synthetic_driver_registration_body(func: &FunctionDef, ops_expr: Expr) -> Block {
    let span = func.span;
    let is_native_lib = driver_manifest_attr(func).is_some_and(|attr| attr.name == "native_lib");
    let version_fallback_idx = if is_native_lib { 1 } else { 3 };
    let version_expr =
        driver_attr_arg(func, "version", version_fallback_idx).unwrap_or_else(|| Expr::String("0.1".to_string()));
    let manifest_call = if is_native_lib {
        Expr::MethodCall {
            receiver: Box::new(Expr::Identifier("DriverManifest".to_string())),
            method: "for_native_lib".to_string(),
            args: vec![
                positional_arg(Expr::String(func.name.clone()), span),
                positional_arg(version_expr, span),
            ],
            generic_args: vec![],
        }
    } else {
        let class_expr = driver_attr_arg(func, "class", 0)
            .or_else(|| driver_attr_arg(func, "dclass", 0))
            .unwrap_or(Expr::Integer(0));
        let vendor_expr = driver_attr_arg(func, "vendor", 1).unwrap_or(Expr::Integer(0));
        let device_expr = driver_attr_arg(func, "device", 2)
            .or_else(|| driver_attr_arg(func, "devices", 2))
            .unwrap_or_else(|| Expr::Array(vec![]));

        Expr::MethodCall {
            receiver: Box::new(Expr::Identifier("DriverManifest".to_string())),
            method: "for_driver".to_string(),
            args: vec![
                positional_arg(Expr::String(func.name.clone()), span),
                positional_arg(version_expr, span),
                positional_arg(class_expr, span),
                positional_arg(vendor_expr, span),
                positional_arg(device_expr, span),
            ],
            generic_args: vec![],
        }
    };
    let register_call = Expr::Call {
        callee: Box::new(Expr::Identifier("register_static_driver".to_string())),
        args: vec![
            positional_arg(Expr::Identifier("m".to_string()), span),
            positional_arg(Expr::Identifier("ops".to_string()), span),
        ],
    };

    Block {
        span,
        statements: vec![
            Node::Let(LetStmt {
                span,
                pattern: Pattern::Identifier("m".to_string()),
                ty: None,
                value: Some(manifest_call),
                mutability: Mutability::Immutable,
                storage_class: StorageClass::Auto,
                is_ghost: false,
                is_suspend: false,
            }),
            Node::Let(LetStmt {
                span,
                pattern: Pattern::Identifier("ops".to_string()),
                ty: None,
                value: Some(ops_expr),
                mutability: Mutability::Immutable,
                storage_class: StorageClass::Auto,
                is_ghost: false,
                is_suspend: false,
            }),
            Node::Return(ReturnStmt {
                span,
                value: Some(register_call),
            }),
        ],
    }
}

fn effective_function_body(func: &FunctionDef) -> Option<Block> {
    if is_driver_stub_body(&func.body) {
        driver_ops_arg(func).map(|ops_expr| synthetic_driver_registration_body(func, ops_expr))
    } else {
        None
    }
}

/// Execute a function body with bound arguments in a local environment.
///
/// This helper consolidates the common pattern of:
/// 1. Inserting bound arguments into local environment
/// 2. Executing the function body
/// 3. Validating the return type
/// 4. Wrapping in Promise if async
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn execute_function_body(
    func: &FunctionDef,
    bound_args: HashMap<String, Value>,
    local_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    wrap_async: bool,
) -> Result<Value, CompileError> {
    // Coverage tracking - enabled via SIMPLE_COVERAGE env var.
    //
    // This is the SINGLE choke point every interpreted function body passes
    // through, so it is the only place the collector's `functions` section can
    // see instance-method dispatch. The recording used to live in the three
    // `exec_function*_inner` helpers plus the writeback variant, all of which
    // are plain-call paths; `exec_function_with_values_and_self` (class/enum
    // method dispatch), `exec_function_with_captured_env` (closures/lambdas),
    // `interpreter_control::exec_method_body` (with-statement + `call_method_if_exists`)
    // and `interpreter_method::special::execution::exec_function_with_self_return`
    // (mutating-self dispatch) all reach a body WITHOUT going through them, so
    // a `me name()` body never entered the map and the reporter's
    // called-function gate scored it 0 however thoroughly it was tested. See
    // the KNOWN CAP note in src/app/test_runner_new/test_runner_single.spl.
    //
    // Recording here rather than at each entry point is also what keeps the
    // call counts honest: every one of those entry points funnels into exactly
    // one `execute_function_body` call, so moving the hook down (and deleting
    // the four upstream copies) preserves the previous counts exactly instead
    // of double-counting the paths that already recorded.
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }
    // Big-alloc attribution: name the interpreted function on a TLS stack so an
    // oversized-allocation report can say WHICH .spl function's loop allocated.
    // No-op (one cached-bool branch) unless the guard is enabled.
    let _mem_frame = crate::mem_trace::InterpFrame::enter(&func.name);

    // Stack overflow detection: push depth, auto-pop on drop
    let _depth_guard = crate::interpreter::push_call_depth(&func.name)?;

    // Save current CONST_NAMES and IMMUTABLE_VARS, clear for function scope
    // Use std::mem::take to swap+clear in one step (avoids clone allocation)
    let saved_const_names = CONST_NAMES.with(|cell| std::mem::take(&mut *cell.borrow_mut()));
    let saved_immutable_vars = IMMUTABLE_VARS.with(|cell| std::mem::take(&mut *cell.borrow_mut()));
    if let Some(traced) = crate::interpreter::const_trace_target() {
        if saved_const_names.contains(traced) {
            eprintln!(
                "[const-trace] fnexec:take fn={} saved-set-contains={}",
                func.name, traced
            );
        }
    }

    // Track which module's function is currently executing (innermost frame),
    // used only to break ties in unqualified same-name/same-arity overload
    // resolution (see `select_overload` in interpreter_call/mod.rs). If this
    // function has no recorded owner (e.g. a lambda), leave the inherited
    // value from the caller's frame untouched rather than clearing it.
    let func_owner_module = function_module_owner(func);
    let saved_exec_module = CURRENT_EXEC_MODULE.with(|cell| {
        let mut current = cell.borrow_mut();
        let saved = current.clone();
        if let Some(owner) = &func_owner_module {
            *current = Some(Arc::clone(owner));
        }
        saved
    });
    if simple_runtime::value::heap::rt_mem_attr_enabled() != 0 {
        if let Some(owner) = &func_owner_module {
            simple_runtime::value::heap::set_current_owner(owner.as_ref());
        }
    }

    // Check if this is an immutable fn method (has self but not is_me_method)
    // Save and set IN_IMMUTABLE_FN_METHOD flag in single borrow
    let is_method_with_self = local_env.contains_key("self") || bound_args.contains_key("self");
    let is_immutable_fn_method = is_method_with_self && !func.is_me_method;
    let saved_in_immutable_fn = IN_IMMUTABLE_FN_METHOD.with(|cell| {
        let mut flag = cell.borrow_mut();
        let saved = *flag;
        *flag = is_immutable_fn_method;
        saved
    });

    for param in &func.params {
        local_env.mark_local(param.name.clone());
    }

    // Insert bound arguments into environment
    for (name, val) in bound_args {
        local_env.insert(name, val);
    }

    // Generator function support: set up GENERATOR_YIELDS before execution
    if func.is_generator {
        GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = Some(Vec::new()));
    }

    let synthetic_body = effective_function_body(func);
    let body = synthetic_body.as_ref().unwrap_or(&func.body);
    mark_block_locals(body, local_env);

    // Execute function body - handle result manually to ensure flag restoration
    let exec_result = exec_block_fn(body, local_env, functions, classes, enums, impl_methods);

    // ALWAYS restore flags before handling the result to avoid flag leaking on error
    IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow_mut() = saved_in_immutable_fn);
    if let Some(traced) = crate::interpreter::const_trace_target() {
        let live_has = CONST_NAMES.with(|cell| cell.borrow().contains(traced));
        if live_has || saved_const_names.contains(traced) {
            eprintln!(
                "[const-trace] fnexec:restore fn={} live-had={} restoring-to-contains={}",
                func.name,
                live_has,
                saved_const_names.contains(traced)
            );
        }
    }
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
    if simple_runtime::value::heap::rt_mem_attr_enabled() != 0 {
        if let Some(owner) = &saved_exec_module {
            simple_runtime::value::heap::set_current_owner(owner.as_ref());
        }
    }
    CURRENT_EXEC_MODULE.with(|cell| *cell.borrow_mut() = saved_exec_module);

    // Generator function: collect yields and return GeneratorValue
    if func.is_generator {
        let yields = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
        let gen = GeneratorValue::new_with_values(yields);
        return Ok(Value::Generator(gen));
    }

    // Now extract result, potentially returning error.
    // The ORIGIN of the value is tracked alongside it: a body that produced no
    // value at all must not first be laundered into `Value::Nil` (and then, for
    // an optional return type, into `Option::None`). Only a UNIT contract may
    // fall through without a value; every other contract fails closed with
    // E-SFFI-016. Bug:
    // doc/08_tracking/bug/sffi_non_optional_fallthrough_fabricates_nil_2026-08-21.md
    let return_contract = sffi_return_contract(func.return_type.as_ref());
    let (return_origin, extracted) = match exec_result {
        Ok((Control::Return(v), _)) => (
            if matches!(v, Value::Nil) {
                SffiReturnOrigin::ExplicitOptionalNone
            } else {
                SffiReturnOrigin::ExplicitReturn
            },
            Some(v),
        ),
        Ok((_, Some(v))) => (SffiReturnOrigin::TailValue, Some(v)),
        Ok((_, None)) => (
            if matches!(return_contract, SffiReturnContract::Unit) {
                SffiReturnOrigin::UnitFallthrough
            } else {
                SffiReturnOrigin::MissingReturn
            },
            None,
        ),
        Err(CompileError::TryError(val)) => (SffiReturnOrigin::ForeignRawResult, Some(*val)),
        Err(e) => return Err(e),
    };
    let result = match extracted {
        Some(value) => value,
        None => validate_sffi_return_contract(&func.name, func.return_type.as_ref(), return_origin, None)?,
    };

    // Auto-wrap return value in Some() when the declared return type is T? (Optional)
    // and the actual return value is not already an Option enum.
    // This handles `fn f() -> i32?: return 42` without explicit `return Some(42)`.
    let result = if matches!(func.return_type, Some(Type::Optional(_))) {
        match &result {
            Value::Enum { enum_name, .. } if enum_name == "Option" => result,
            Value::Nil => Value::Enum {
                enum_name: "Option".to_string(),
                variant: "None".to_string(),
                payload: None,
            },
            _ => {
                // WRITE side of the enum-payload provenance diagnostic
                // (default off, SIMPLE_DEBUG_ENUM_PAYLOAD=1): the implicit
                // `T -> Option<T>` wrap on a function return, the exact shape
                // behind `emit_call() -> LocalId?`.
                crate::interpreter::note_enum_payload_function(
                    "fn-return-some-wrap", "Option", "Some", 0, &result,
                );
                Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(result)),
                }
            }
        }
    } else if let (
        Some(rt),
        Value::Enum {
            enum_name,
            variant,
            payload,
        },
    ) = (&func.return_type, &result)
    {
        // Symmetric counterpart to the auto-wrap above. When `-> T?` functions
        // Some-wrap their plain returns, callers that funnel that value into a
        // CONCRETE non-Optional return — e.g. `fn require() -> T:
        //   val v = get_opt(); if v != nil: return v` — would otherwise return
        // `Some(v)` where a bare `T` is declared, and any field/method access on
        // the result fails with "… on Option". Unwrap Some(x) -> x when the
        // declared return type is a concrete non-Option type. Only `Some` is
        // unwrapped; `None` against a concrete return type is left for the
        // existing return-type validation to flag.
        if enum_name == "Option" && variant == "Some" && return_type_unwraps_option_some(rt) {
            match payload {
                Some(inner) => (**inner).clone(),
                None => result,
            }
        } else {
            result
        }
    } else {
        result
    };

    // Validate the full return contract (total, not unit-only).
    let result = validate_sffi_return_contract(
        &func.name,
        func.return_type.as_ref(),
        return_origin,
        Some(result),
    )?;

    // Wrap in Promise if async and requested
    let result = if wrap_async && is_async_function(func) {
        wrap_in_promise(result)
    } else {
        result
    };

    Ok(result)
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn exec_function(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &Arc<HashMap<String, Value>>)>,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx)
    })
}

pub(crate) fn exec_function_with_values(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_with_values_inner(func, args, outer_env, functions, classes, enums, impl_methods)
    })
}

#[allow(clippy::too_many_arguments)] // reason: mirrors the other function execution entrypoints
pub(crate) fn exec_function_with_bound_args(
    func: &FunctionDef,
    bound_args: HashMap<String, Value>,
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_with_bound_args_inner(func, bound_args, outer_env, functions, classes, enums, impl_methods)
    })
}

/// Like `exec_function_with_values`, but also writes mutated `mut`
/// container-typed parameters (Array/Dict/Object/Tuple) back to the caller's
/// bindings — the same write-back `exec_function_inner` performs for the
/// plain single-definition call path (Bug #19's `write_back_mutable_arguments`).
///
/// The unqualified-call overload-resolution path (interpreter_call/mod.rs
/// Priority 4, used whenever `FUNCTION_OVERLOADS[name].len() > 1`) used to
/// call plain `exec_function_with_values` with already-evaluated `Value`s
/// and no caller-side identifier info, so a `mut`-parameter mutation was
/// silently dropped for any call routed through it — including a call to a
/// function with only ONE real definition that happened to be registered
/// twice (e.g. once per module-export unpacking site), which is common for
/// any cross-module `use module.{name}` import. This variant additionally
/// takes the original call-site `Argument` expressions (unevaluated — only
/// used to map a callee parameter back to a caller identifier/field, exactly
/// like `write_back_mutable_arguments`'s normal contract) so the mutation is
/// observed via the same mechanism the non-overloaded path already used. See
/// doc/08_tracking/bug/sspec_it_block_loses_cross_module_class_mutation_2026-07-17.md.
#[allow(clippy::too_many_arguments)] // reason: mirrors exec_function_with_values plus one extra param
pub(crate) fn exec_function_with_values_and_writeback(
    func: &FunctionDef,
    args: &[Value],
    original_args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_with_values_and_writeback_inner(
            func,
            args,
            original_args,
            outer_env,
            functions,
            classes,
            enums,
            impl_methods,
        )
    })
}

/// Execute function with already-evaluated Values and self context for method calls
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn exec_function_with_values_and_self(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &Arc<HashMap<String, Value>>)>,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        publish_and_repoint(outer_env);
        let mut local_env = captured_env_with_live_globals(func, &Env::new());

        // Set up self context if provided
        if let Some((class_name, fields)) = self_ctx {
            // Check if this is an enum method (fields contains just "self")
            if fields.len() == 1 && fields.contains_key("self") {
                // For enum methods, self should be the enum value directly
                local_env.insert("self".into(), fields.get("self").unwrap().clone());
            } else {
                // For class methods, self is an Object — Arc::clone is O(1)
                local_env.insert(
                    "self".into(),
                    Value::Object {
                        class: class_name.to_string(),
                        fields: Arc::clone(fields),
                    },
                );
            }
        }

        let self_mode = if self_ctx.is_some() {
            SelfMode::SkipSelf
        } else {
            SelfMode::IncludeSelf
        };

        let bound = bind_args_with_values(
            &func.params,
            args,
            outer_env,
            functions,
            classes,
            enums,
            impl_methods,
            self_mode,
        )?;

        outer_env.release_scope();
    let result = execute_function_body(
            func,
            bound,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
            false,
        );
        // The callee is done executing: drop its snapshot so the sync below
        // writes the store in place instead of copying the owner map.
        local_env.release_scope();
        sync_owned_captured_globals(func, &local_env, outer_env);
        result
    })
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn exec_function_with_captured_env(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
    captured_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        publish_and_repoint(outer_env);
        let mut local_env = captured_env_with_live_globals(func, captured_env);

        let self_mode = SelfMode::IncludeSelf;
        let bound_args = bind_args(
            &func.params,
            args,
            outer_env,
            functions,
            classes,
            enums,
            impl_methods,
            self_mode,
        )?;

        outer_env.release_scope();
    let result = execute_function_body(
            func,
            bound_args,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
            false,
        );
        // The callee is done executing: drop its snapshot so the sync below
        // writes the store in place instead of copying the owner map.
        local_env.release_scope();
        sync_owned_captured_globals(func, &local_env, outer_env);
        if result.is_ok() {
            write_back_mutable_arguments(func, args, outer_env, &local_env, classes, self_mode);
        }
        result
    })
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
/// True when a function whose body produced an `Option::Some(x)` should have it
/// unwrapped to `x` to satisfy a CONCRETE non-Optional declared return type.
/// Conservative by design: anything that could legitimately hold an Option
/// (`any`, `Option`/`Result`, bare generic params, unions, trait objects, …)
/// is left wrapped. Mirrors the `-> T?` auto-wrap so the two stay in lockstep.
pub(crate) fn return_type_unwraps_option_some(t: &Type) -> bool {
    match t {
        Type::Optional(_) => false,
        Type::Simple(n) => {
            n != "any"
                && n != "Any"
                && n != "Option"
                && n != "Result"
                // exclude lone generic type params (e.g. `T`, `U`)
                && !(n.len() == 1 && n.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
        }
        Type::Generic { name, .. } => name != "Option" && name != "Result",
        Type::Array { .. } | Type::Tuple(_) | Type::LabeledTuple(_) => true,
        Type::Capability { inner, .. } => return_type_unwraps_option_some(inner),
        _ => false,
    }
}

/// True when `v` is an Object whose class was synthesized from a value-type
/// `struct` declaration (ClassDef::is_value_type). Structs have VALUE semantics:
/// callee mutations to a struct parameter must NOT propagate back to the caller,
/// so such values are excluded from the Bug #19 mutable-param write-back. Real
/// `class` values (is_value_type == false) keep REFERENCE semantics and ARE
/// written back. Task #91.
fn is_value_type_struct(v: &Value, classes: &HashMap<String, Arc<ClassDef>>) -> bool {
    matches!(v, Value::Object { class, .. } if classes.get(class).is_some_and(|cd| cd.is_value_type))
}

/// Collection fields of a value-type `struct` are SHARED HANDLES, not copied
/// storage (the "shallow struct copy" resolution, option B of
/// `doc/08_tracking/bug/struct_dict_field_mutation_engine_divergence_2026-08-10.md`).
///
/// Before this, `fn f(self: S, ...)` doing `self.values[k] = v` on a `Dict`/array
/// field was a SILENT NO-OP in the interpreter while the JIT and native/AOT lanes
/// made the write visible — identical source producing opposite state depending
/// on the lane, invisible to any positive assertion. The interpreter models
/// dicts/arrays as `Arc<..>` with copy-on-write, so a callee mutation forks the
/// Arc and dies with the frame unless it is explicitly propagated.
///
/// The propagation is deliberately field-kind-scoped, NOT a whole-struct
/// write-back: scalar and nested-struct fields keep strict value semantics (a
/// callee writing `self.count = 1` still cannot reach the caller), which is what
/// "struct is a value type" means and what task #91 established. Only
/// container-valued fields — the ones the compiled lanes back with a real heap
/// handle — are carried back, which is exactly what makes the three engines
/// agree.
/// Returns true when any field of `caller_val` was replaced. Containers are
/// compared by HANDLE identity (`Arc::ptr_eq`), never by content: a deep
/// `PartialEq` here walked every token of a parser object's array on every
/// method call (the top frame in 4/5 samples of `lint driver_types.spl`
/// once per-call env setup was O(args)). A handle that changed carries the
/// callee's new container; writing back a value-equal one is observably a
/// no-op, so identity is the right — and O(1) — test.
fn merge_shared_collection_fields(caller_val: &mut Value, callee_val: &Value) -> bool {
    let (Value::Object { fields: caller_fields, .. }, Value::Object { fields: callee_fields, .. }) =
        (&mut *caller_val, callee_val)
    else {
        return false;
    };
    if Arc::ptr_eq(caller_fields, callee_fields) {
        return false;
    }
    let mut updates: Vec<(String, Value)> = Vec::new();
    for (name, new_field) in callee_fields.iter() {
        let Some(old_field) = caller_fields.get(name) else {
            continue;
        };
        match (old_field, new_field) {
            (Value::Array(old), Value::Array(new)) if !Arc::ptr_eq(old, new) => {
                updates.push((name.clone(), new_field.clone()));
            }
            (Value::Dict(old), Value::Dict(new)) if !Arc::ptr_eq(old, new) => {
                updates.push((name.clone(), new_field.clone()));
            }
            (Value::ByteArray(old), Value::ByteArray(new)) if !Arc::ptr_eq(old, new) => {
                updates.push((name.clone(), new_field.clone()));
            }
            // A struct-typed field is itself value-copied, but the containers
            // NESTED inside it are still shared handles, so recurse rather than
            // stopping at depth one. `self.inner.values[k] = v` through a
            // by-value receiver must reach the caller for the same reason
            // `self.values[k] = v` does.
            (Value::Object { .. }, Value::Object { .. }) => {
                let mut merged = old_field.clone();
                if merge_shared_collection_fields(&mut merged, new_field) {
                    updates.push((name.clone(), merged));
                }
            }
            _ => {}
        }
    }
    if updates.is_empty() {
        return false;
    }
    let slots = Arc::make_mut(caller_fields);
    for (name, value) in updates {
        slots.insert(name, value);
    }
    true
}

// Bug #19 fix: write back mutable-container parameters to caller's bindings.
//
// When a function is called with a simple identifier argument (e.g., `f(a)`)
// and the parameter is a mutable container type (Array / Dict / Object /
// Tuple), any mutation the callee performed to its local parameter binding
// should be observed by the caller. The interpreter stores arrays / dicts /
// objects as `Arc<_>` with copy-on-write semantics, so mutations inside the
// callee produce a new Arc in the callee's local env and are NOT visible to
// the caller unless we explicitly propagate the final callee value back.
//
// This is only done for identifier arguments and positional one-level field
// arguments, and only for container types; primitives keep value semantics.
fn write_back_mutable_arguments(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
    local_env: &Env,
    classes: &HashMap<String, Arc<ClassDef>>,
    self_mode: SelfMode,
) {
    let params_to_bind: Vec<_> = func
        .params
        .iter()
        .filter(|p| !(self_mode == SelfMode::SkipSelf && p.name == METHOD_SELF))
        .collect();
    let mut positional_idx = 0usize;
    let mut positional_mapping_valid = true;
    // Caller bindings already written back on behalf of a `mut` parameter.
    // When the SAME caller variable is passed to both a `mut` and a non-`mut`
    // parameter (aliasing, e.g. `touch(arr, arr)` against
    // `fn touch(mut a: [i64], b: [i64])`), the non-`mut` parameter still holds
    // the pre-call snapshot. Writing that snapshot back afterwards silently
    // reverts the mutation the `mut` parameter legitimately made, with no
    // diagnostic and exit code 0. Track the mutated names and never let a
    // non-`mut` parameter clobber one.
    let mut mut_written: std::collections::HashSet<String> = std::collections::HashSet::new();
    for arg in args {
        // A spread can bind multiple parameters, so later positional arguments
        // cannot be reconstructed safely without binder provenance. Named
        // arguments remain safe because they identify their parameter.
        if matches!(&arg.value, simple_parser::ast::Expr::Spread(_)) {
            positional_mapping_valid = false;
            continue;
        }
        // Determine the caller binding name and the callee parameter name.
        // For FieldAccess args (e.g., `self.values`), we track separately
        // so we can write back into the object field after the call.
        enum ArgSource {
            Ident {
                caller_name: String,
                param_name: String,
            },
            Field {
                obj_name: String,
                field_name: String,
                param_name: String,
            },
        }
        let source = if let Some(name) = &arg.name {
            // Named argument: match param by name
            if params_to_bind.iter().any(|p| p.name == name.as_str() && p.variadic) {
                continue;
            }
            if let simple_parser::ast::Expr::Identifier(caller) = &arg.value {
                ArgSource::Ident {
                    caller_name: caller.clone(),
                    param_name: name.clone(),
                }
            } else {
                continue;
            }
        } else {
            if !positional_mapping_valid {
                continue;
            }
            let param = match params_to_bind.get(positional_idx) {
                Some(p) => p,
                None => {
                    positional_idx += 1;
                    continue;
                }
            };
            positional_idx += 1;
            if param.variadic {
                positional_mapping_valid = false;
                continue;
            }
            if let simple_parser::ast::Expr::Identifier(caller) = &arg.value {
                ArgSource::Ident {
                    caller_name: caller.clone(),
                    param_name: param.name.clone(),
                }
            } else if let simple_parser::ast::Expr::FieldAccess { receiver, field } = &arg.value {
                if let simple_parser::ast::Expr::Identifier(obj) = receiver.as_ref() {
                    ArgSource::Field {
                        obj_name: obj.clone(),
                        field_name: field.clone(),
                        param_name: param.name.clone(),
                    }
                } else {
                    continue;
                }
            } else {
                continue;
            }
        };
        match source {
            ArgSource::Ident {
                caller_name,
                param_name,
            } => {
                if caller_name == METHOD_SELF && self_mode == SelfMode::SkipSelf {
                    continue;
                }
                let param_is_mut = params_to_bind
                    .iter()
                    .find(|p| p.name == param_name)
                    .map(|p| p.mutability.is_mutable())
                    .unwrap_or(false);
                // Aliased argument: a non-`mut` parameter must never overwrite a
                // caller binding that a `mut` parameter has already updated.
                if !param_is_mut && mut_written.contains(&caller_name) {
                    continue;
                }
                if let Some(callee_val) = local_env.get(&param_name) {
                    // Value-type structs (task #91) keep VALUE semantics: never
                    // write callee mutations back to the caller's binding.
                    if !is_value_type_struct(callee_val, classes)
                        && matches!(
                            callee_val,
                            Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                        )
                        && outer_env.contains_key(&caller_name)
                    {
                        let new_val = callee_val.clone();
                        if param_is_mut {
                            mut_written.insert(caller_name.clone());
                        }
                        outer_env.insert(caller_name, new_val);
                    } else if is_value_type_struct(callee_val, classes) {
                        // Value-type struct: fields stay value-copied, but its
                        // container-valued fields are shared handles. See
                        // merge_shared_collection_fields.
                        if let Some(mut caller_val) = outer_env.get(&caller_name).cloned() {
                            if merge_shared_collection_fields(&mut caller_val, callee_val) {
                                outer_env.insert(caller_name, caller_val);
                            }
                        }
                    }
                }
            }
            ArgSource::Field {
                obj_name,
                field_name,
                param_name,
            } => {
                // Write back mutated field value into the caller's object.
                // e.g., `write_first(self.values, next)` — after the call,
                // write the callee's `values` param back into `self.values`.
                if let Some(callee_val) = local_env.get(&param_name).cloned() {
                    // Value-type structs (task #91) keep VALUE semantics: a
                    // struct passed as `obj.field` is not mutated back either.
                    if !is_value_type_struct(&callee_val, classes)
                        && matches!(
                            callee_val,
                            Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                        )
                    {
                        if let Some(obj_val) = outer_env.get(&obj_name).cloned() {
                            if let Value::Object { class, mut fields } = obj_val {
                                Arc::make_mut(&mut fields).insert(field_name, callee_val);
                                outer_env.insert(obj_name, Value::Object { class, fields });
                            }
                        }
                    }
                }
            }
        }
    }
}

fn exec_function_inner(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &Arc<HashMap<String, Value>>)>,
) -> Result<Value, CompileError> {
    let trace_start = trace_interpreter_call_enter(func);

    // Layout recording for 4KB page locality optimization
    crate::layout_recorder::record_function_call(&func.name);

    // Diagram tracing for call flow profiling
    if diagram_sffi::is_diagram_enabled() {
        if let Some((class_name, _)) = self_ctx {
            // Method call on a class
            diagram_sffi::trace_method(class_name, &func.name);
        } else {
            // Free function call
            diagram_sffi::trace_call(&func.name);
        }
    }

    // Runtime profiler hooks
    if crate::runtime_profile::is_profiling_active() {
        let call_type = if self_ctx.is_some() {
            crate::runtime_profile::CallType::Method
        } else {
            crate::runtime_profile::CallType::Direct
        };
        crate::runtime_profile::record_full_call(&func.name, self_ctx.map(|(c, _)| c), vec![], call_type);
    }

    publish_and_repoint(outer_env);
    let mut local_env = captured_env_with_live_globals(func, &Env::new());

    if let Some((class_name, fields)) = self_ctx {
        // Check if this is an enum method (fields contains just "self")
        if fields.len() == 1 && fields.contains_key("self") {
            // For enum methods, self should be the enum value directly, not wrapped in Object
            let self_val = fields.get("self").unwrap().clone();
            local_env.insert("self".into(), self_val);
        } else {
            // For class methods, self is an Object — Arc::clone is O(1)
            local_env.insert(
                "self".into(),
                Value::Object {
                    class: class_name.to_string(),
                    fields: Arc::clone(fields),
                },
            );
        }
    }
    let self_mode = if self_ctx.is_some() {
        SelfMode::SkipSelf
    } else {
        SelfMode::IncludeSelf
    };
    let bound = bind_args(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;

    // Record function return for layout call graph tracking
    crate::layout_recorder::record_function_return();

    outer_env.release_scope();
    let result = execute_function_body(
        func,
        bound,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
        true,
    );
    // The callee is done executing: drop its snapshot so the sync below
    // writes the store in place instead of copying the owner map.
    local_env.release_scope();
    sync_owned_captured_globals(func, &local_env, outer_env);

    if result.is_ok() {
        write_back_mutable_arguments(func, args, outer_env, &local_env, classes, self_mode);
    }

    // Runtime profiler return hook
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

    trace_interpreter_call_exit(trace_start, &func.name, if result.is_ok() { "ok" } else { "err" });

    result
}

#[allow(clippy::too_many_arguments)] // reason: mirrors exec_function_with_values_inner plus one extra param
fn exec_function_with_values_and_writeback_inner(
    func: &FunctionDef,
    args: &[Value],
    original_args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let trace_start = trace_interpreter_call_enter(func);

    crate::layout_recorder::record_function_call(&func.name);

    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_call(&func.name);
    }

    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_call(&func.name, None, vec![], crate::runtime_profile::CallType::Direct);
    }

    publish_and_repoint(outer_env);
    let mut local_env = captured_env_with_live_globals(func, &Env::new());
    let self_mode = SelfMode::IncludeSelf;
    let bound = bind_args_with_values(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;

    crate::layout_recorder::record_function_return();

    outer_env.release_scope();
    let result = execute_function_body(
        func,
        bound,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
        true,
    );
    // The callee is done executing: drop its snapshot so the sync below
    // writes the store in place instead of copying the owner map.
    local_env.release_scope();
    sync_owned_captured_globals(func, &local_env, outer_env);

    if result.is_ok() {
        write_back_mutable_arguments(func, original_args, outer_env, &local_env, classes, self_mode);
    }

    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

    trace_interpreter_call_exit(trace_start, &func.name, if result.is_ok() { "ok" } else { "err" });

    result
}

fn exec_function_with_values_inner(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let self_mode = SelfMode::IncludeSelf;
    let bound = bind_args_with_values(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;
    exec_function_with_bound_args_inner(func, bound, outer_env, functions, classes, enums, impl_methods)
}

#[allow(clippy::too_many_arguments)] // reason: shared core for already-bound function execution
fn exec_function_with_bound_args_inner(
    func: &FunctionDef,
    bound_args: HashMap<String, Value>,
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let trace_start = trace_interpreter_call_enter(func);

    // Layout recording for 4KB page locality optimization
    crate::layout_recorder::record_function_call(&func.name);

    // Diagram tracing for call flow profiling
    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_call(&func.name);
    }

    // Runtime profiler hooks
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_call(&func.name, None, vec![], crate::runtime_profile::CallType::Direct);
    }

    publish_and_repoint(outer_env);
    let mut local_env = captured_env_with_live_globals(func, &Env::new());
    // Record function return for layout call graph tracking
    crate::layout_recorder::record_function_return();

    outer_env.release_scope();
    let result = execute_function_body(
        func,
        bound_args,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
        true,
    );
    // The callee is done executing: drop its snapshot so the sync below
    // writes the store in place instead of copying the owner map.
    local_env.release_scope();
    sync_owned_captured_globals(func, &local_env, outer_env);

    // Runtime profiler return hook
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

    trace_interpreter_call_exit(trace_start, &func.name, if result.is_ok() { "ok" } else { "err" });

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    #[test]
    fn sffi_return_contract_rejects_missing_non_optional_return() {
        let error = validate_sffi_return_contract(
            "missing_text",
            Some(&Type::Simple("text".to_string())),
            SffiReturnOrigin::MissingReturn,
            None,
        )
        .expect_err("non-optional fallthrough must fail closed");
        assert!(error
            .to_string()
            .contains("missing return in non-unit function 'missing_text'"));
    }

    #[test]
    fn sffi_return_contract_preserves_unit_fallthrough() {
        let value = validate_sffi_return_contract("unit_fn", None, SffiReturnOrigin::UnitFallthrough, None)
            .expect("unit fallthrough is valid");
        assert_eq!(value, Value::Nil);
    }

    #[test]
    fn sffi_return_contract_preserves_explicit_unit_fallthrough() {
        let explicit_unit = Type::Tuple(Vec::new());
        let value = validate_sffi_return_contract(
            "explicit_unit_fn",
            Some(&explicit_unit),
            SffiReturnOrigin::UnitFallthrough,
            None,
        )
        .expect("explicit Unit fallthrough is valid");
        assert_eq!(value, Value::Nil);
    }

    #[test]
    fn sffi_return_contract_preserves_explicit_optional_nil() {
        let optional = Type::Optional(Box::new(Type::Simple("text".to_string())));
        let value = validate_sffi_return_contract(
            "optional_fn",
            Some(&optional),
            SffiReturnOrigin::ExplicitOptionalNone,
            Some(Value::Nil),
        )
        .expect("explicit optional nil is valid");
        assert_eq!(value, Value::Nil);
    }

    #[test]
    fn sffi_return_contract_preserves_explicit_generic_option_nil() {
        // Explicit generic spelling `Option<T>` (as opposed to the `T?` sugar,
        // which parses to `Type::Optional`) must be classified as Optional
        // too, or `return nil` faults with the non-optional contract error.
        let generic_option = Type::Generic {
            name: "Option".to_string(),
            args: vec![Type::Simple("i64".to_string())],
        };
        let value = validate_sffi_return_contract(
            "generic_option_fn",
            Some(&generic_option),
            SffiReturnOrigin::ExplicitOptionalNone,
            Some(Value::Nil),
        )
        .expect("explicit Option<T> nil is valid");
        assert_eq!(value, Value::Nil);
    }

    #[test]
    fn sffi_return_contract_rejects_explicit_nil_for_non_optional_return() {
        let error = validate_sffi_return_contract(
            "non_optional_text",
            Some(&Type::Simple("text".to_string())),
            SffiReturnOrigin::ExplicitReturn,
            Some(Value::Nil),
        )
        .expect_err("non-optional return must reject nil");
        assert!(error
            .to_string()
            .contains("nil is forbidden by the non-optional return contract"));
    }

    #[test]
    fn refreshed_globals_do_not_clobber_newer_callee_writes() {
        let mut parser = Parser::new("fn probe():\n    0\n");
        let module = parser.parse().expect("parse probe");
        let function = module
            .items
            .into_iter()
            .find_map(|node| match node {
                Node::Function(function) => Some(function),
                _ => None,
            })
            .expect("probe function");
        let owner: Arc<str> = Arc::from("test/module_global_refresh.spl");
        let function_key = &function as *const FunctionDef as usize;

        FUNCTION_MODULE_OWNER.with(|cell| {
            cell.borrow_mut().insert(function_key, Arc::clone(&owner));
        });
        CURRENT_EXEC_MODULE.with(|cell| *cell.borrow_mut() = Some(Arc::clone(&owner)));
        if simple_runtime::value::heap::rt_mem_attr_enabled() != 0 {
            simple_runtime::value::heap::set_current_owner(owner.as_ref());
        }
        MODULE_GLOBALS.with(|cell| cell.borrow_mut().clear());
        set_owned_global(&owner, "stale", Value::Bool(false), true);
        set_owned_global(&owner, "caller_write", Value::Bool(true), true);
        set_owned_global(&owner, "items", Value::array(vec![Value::Int(1)]), true);

        let mut frame = Env::new();
        frame.refresh_globals([
            ("stale".to_string(), Value::Bool(false)),
            ("caller_write".to_string(), Value::Bool(true)),
            ("items".to_string(), Value::array(vec![Value::Int(1)])),
        ]);
        assert!(set_owned_global(&owner, "stale", Value::Bool(true), false));
        frame.insert("caller_write".to_string(), Value::Bool(false));
        let Value::Array(items) = frame.get_mut("items").expect("items") else {
            panic!("items must be an array");
        };
        Arc::make_mut(items).push(Value::Int(2));

        let mut outer = Env::new();
        sync_owned_captured_globals(&function, &frame, &mut outer);

        assert_eq!(outer.get("stale"), Some(&Value::Bool(true)));
        assert!(outer.is_refreshed_global("stale"));

        assert_eq!(owned_global(&owner, "stale"), Some(Value::Bool(true)));
        assert_eq!(owned_global(&owner, "caller_write"), Some(Value::Bool(false)));
        let Some(Value::Array(items)) = owned_global(&owner, "items") else {
            panic!("items must be an array");
        };
        assert_eq!(items.as_slice(), &[Value::Int(1), Value::Int(2)]);

        let foreign_owner: Arc<str> = Arc::from("test/foreign_frame.spl");
        FUNCTION_MODULE_OWNER.with(|cell| {
            cell.borrow_mut().insert(function_key, Arc::clone(&foreign_owner));
        });
        seed_owner_globals(&foreign_owner);
        let mut foreign_frame = Env::new();
        foreign_frame.forward_globals(Arc::clone(&owner), [("stale".to_string(), Value::Bool(false))]);
        let mut owner_frame = Env::new();
        sync_owned_captured_globals(&function, &foreign_frame, &mut owner_frame);
        assert_eq!(owner_frame.get("stale"), Some(&Value::Bool(true)));

        FUNCTION_MODULE_OWNER.with(|cell| cell.borrow_mut().remove(&function_key));
        crate::interpreter::MODULE_GLOBALS_BY_OWNER.with(|cell| {
            let mut globals = cell.borrow_mut();
            let globals = Arc::make_mut(&mut *globals);
            globals.remove(&owner);
            globals.remove(&foreign_owner);
        });
        MODULE_GLOBALS.with(|cell| cell.borrow_mut().clear());
        CURRENT_EXEC_MODULE.with(|cell| *cell.borrow_mut() = None);
    }
}
