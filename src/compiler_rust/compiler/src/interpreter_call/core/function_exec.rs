// Core function execution logic

use super::arg_binding::{bind_args, bind_args_with_values};
use super::async_support::{is_async_function, wrap_in_promise};
use super::macros::*;
use crate::error::CompileError;
use crate::interpreter::{
    exec_block_fn, Control, CONST_NAMES, IMMUTABLE_VARS, IN_IMMUTABLE_FN_METHOD, GENERATOR_YIELDS, CURRENT_EXEC_MODULE,
    FUNCTION_MODULE_OWNER, MODULE_ENV_BY_OWNER, MODULE_GLOBALS, MODULE_GLOBALS_BY_OWNER,
    MODULE_GLOBALS_INITIAL_BY_OWNER, visit_pattern_binding_names,
};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{
    Argument, Attribute, Block, ClassDef, EnumDef, Expr, FunctionDef, LetStmt, Mutability, Node, Pattern, ReturnStmt,
    SelfMode, StorageClass, Type,
};
use simple_runtime::value::diagram_sffi;
use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, LazyLock};
use std::time::Instant;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

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

fn captured_env_with_live_globals(func: &FunctionDef, captured_env: &Env) -> Env {
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

    let initial_owner_globals =
        MODULE_GLOBALS_INITIAL_BY_OWNER.with(|cell| cell.borrow().get(&owner).cloned().unwrap_or_default());
    let owner_globals = MODULE_GLOBALS_BY_OWNER.with(|cell| {
        cell.borrow_mut()
            .entry(Arc::clone(&owner))
            .or_insert(initial_owner_globals)
            .clone()
    });
    let mut base = if captured_env.is_empty() {
        MODULE_ENV_BY_OWNER
            .with(|cell| cell.borrow().get(&owner).cloned())
            .map(|env| (*env).clone())
            .unwrap_or_default()
    } else {
        captured_env.to_map()
    };
    base.extend(owner_globals);
    Env::with_base(Arc::new(base))
}

fn sync_owned_captured_globals(func: &FunctionDef, local_env: &Env, outer_env: &mut Env) {
    let Some(owner) = function_module_owner(func) else {
        return;
    };
    let changed = MODULE_GLOBALS_BY_OWNER.with(|cell| {
        let mut globals_by_owner = cell.borrow_mut();
        let Some(owner_globals) = globals_by_owner.get_mut(&owner) else {
            return Vec::new();
        };
        let changed = local_env
            .overlay_entries()
            .filter_map(|(name, value)| {
                if !owner_globals.contains_key(name)
                    || func.params.iter().any(|param| param.name == *name)
                    || local_env.is_local(name)
                {
                    return None;
                }
                Some((name.clone(), value.clone()))
            })
            .collect::<Vec<_>>();
        for (name, value) in &changed {
            owner_globals.insert(name.clone(), value.clone());
        }
        changed
    });
    let caller_has_same_owner =
        CURRENT_EXEC_MODULE.with(|cell| cell.borrow().as_ref().is_some_and(|current| current == &owner));
    if caller_has_same_owner {
        let refreshed = changed
            .into_iter()
            .filter(|(name, _)| !outer_env.is_local(name))
            .collect::<Vec<_>>();
        outer_env.extend(refreshed);
    }
}

fn mark_pattern_locals(pattern: &Pattern, env: &mut Env) {
    visit_pattern_binding_names(pattern, &mut |name| env.mark_local(name.to_owned()));
}

fn mark_block_locals(block: &Block, env: &mut Env) {
    for node in &block.statements {
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
fn execute_function_body(
    func: &FunctionDef,
    bound_args: HashMap<String, Value>,
    local_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    wrap_async: bool,
) -> Result<Value, CompileError> {
    // Stack overflow detection: push depth, auto-pop on drop
    let _depth_guard = crate::interpreter::push_call_depth(&func.name)?;

    // Save current CONST_NAMES and IMMUTABLE_VARS, clear for function scope
    // Use std::mem::take to swap+clear in one step (avoids clone allocation)
    let saved_const_names = CONST_NAMES.with(|cell| std::mem::take(&mut *cell.borrow_mut()));
    let saved_immutable_vars = IMMUTABLE_VARS.with(|cell| std::mem::take(&mut *cell.borrow_mut()));
    if let Some(traced) = crate::interpreter::const_trace_target() {
        if saved_const_names.contains(traced) {
            eprintln!("[const-trace] fnexec:take fn={} saved-set-contains={}", func.name, traced);
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
            eprintln!("[const-trace] fnexec:restore fn={} live-had={} restoring-to-contains={}", func.name, live_has, saved_const_names.contains(traced));
        }
    }
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
    CURRENT_EXEC_MODULE.with(|cell| *cell.borrow_mut() = saved_exec_module);

    // Generator function: collect yields and return GeneratorValue
    if func.is_generator {
        let yields = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
        let gen = GeneratorValue::new_with_values(yields);
        return Ok(Value::Generator(gen));
    }

    // Now extract result, potentially returning error
    let result = match exec_result {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => *val,
        Err(e) => return Err(e),
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
            _ => Value::Enum {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Some(Box::new(result)),
            },
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

    // Validate return type
    validate_unit!(
        &result,
        func.return_type.as_ref(),
        format!("return type mismatch in '{}'", func.name)
    );

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
        exec_function_with_bound_args_inner(
            func,
            bound_args,
            outer_env,
            functions,
            classes,
            enums,
            impl_methods,
        )
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
                        outer_env.insert(caller_name, new_val);
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

    // Coverage tracking - enabled via SIMPLE_COVERAGE env var
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

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

    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

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

    // Coverage tracking - enabled via SIMPLE_COVERAGE env var
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

    let mut local_env = captured_env_with_live_globals(func, &Env::new());
    // Record function return for layout call graph tracking
    crate::layout_recorder::record_function_return();

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
    sync_owned_captured_globals(func, &local_env, outer_env);

    // Runtime profiler return hook
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

    trace_interpreter_call_exit(trace_start, &func.name, if result.is_ok() { "ok" } else { "err" });

    result
}
