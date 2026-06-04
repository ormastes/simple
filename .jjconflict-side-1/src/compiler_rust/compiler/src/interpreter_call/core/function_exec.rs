// Core function execution logic

use super::arg_binding::{bind_args, bind_args_with_values};
use super::async_support::{is_async_function, wrap_in_promise};
use super::macros::*;
use crate::error::CompileError;
use crate::interpreter::{exec_block_fn, Control, CONST_NAMES, IMMUTABLE_VARS, IN_IMMUTABLE_FN_METHOD, GENERATOR_YIELDS};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{
    Argument, Attribute, Block, ClassDef, EnumDef, Expr, FunctionDef, LetStmt, Mutability, Node, Pattern, ReturnStmt,
    SelfMode, StorageClass, Type,
};
use simple_runtime::value::diagram_sffi;
use std::collections::HashMap;
use std::sync::Arc;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

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

    // Execute function body - handle result manually to ensure flag restoration
    let exec_result = exec_block_fn(body, local_env, functions, classes, enums, impl_methods);

    // ALWAYS restore flags before handling the result to avoid flag leaking on error
    IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow_mut() = saved_in_immutable_fn);
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);

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
        let mut local_env = Env::new();

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

        execute_function_body(
            func,
            bound,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
            false,
        )
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
        let mut local_env = captured_env.clone();

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

        execute_function_body(
            func,
            bound_args,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
            false,
        )
    })
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
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

    let mut local_env = Env::new();

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
    // This is only done for identifier arguments (pass-by-name) and only for
    // container types; primitives keep value semantics.
    if result.is_ok() {
        let params_to_bind: Vec<_> = func
            .params
            .iter()
            .filter(|p| !(self_ctx.is_some() && p.name == METHOD_SELF))
            .collect();
        let mut positional_idx = 0usize;
        for arg in args {
            // Skip spread expressions — they don't map 1:1 to a caller binding.
            if matches!(&arg.value, simple_parser::ast::Expr::Spread(_)) {
                positional_idx += 1;
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
                if let simple_parser::ast::Expr::Identifier(caller) = &arg.value {
                    ArgSource::Ident {
                        caller_name: caller.clone(),
                        param_name: name.clone(),
                    }
                } else {
                    continue;
                }
            } else {
                let param = match params_to_bind.get(positional_idx) {
                    Some(p) => p,
                    None => {
                        positional_idx += 1;
                        continue;
                    }
                };
                positional_idx += 1;
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
                    if caller_name == METHOD_SELF && self_ctx.is_some() {
                        continue;
                    }
                    if let Some(callee_val) = local_env.get(&param_name) {
                        if matches!(
                            callee_val,
                            Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                        ) && outer_env.contains_key(&caller_name)
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
                        if matches!(
                            callee_val,
                            Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                        ) {
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

    // Runtime profiler return hook
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

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

    let mut local_env = Env::new();
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

    // Runtime profiler return hook
    if crate::runtime_profile::is_profiling_active() {
        crate::runtime_profile::record_full_return(None);
    }

    result
}
