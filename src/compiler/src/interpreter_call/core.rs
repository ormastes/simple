// Core function execution for interpreter
// Function binding, lambda execution, function call logic

use crate::aop_config::AopConfig;
use crate::di::DiScope;
use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, exec_block, exec_block_fn, with_effect_context, Control, get_aop_config, get_di_config, DI_SINGLETONS};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{Argument, Parameter, Type, SelfMode, FunctionDef, ClassDef, EnumDef};
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";
const METHOD_NEW: &str = "new";

pub(crate) fn bind_args(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    bind_args_with_injected(
        params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
        &HashMap::new(),
    )
}

pub(crate) fn bind_args_with_injected(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
    injected: &HashMap<String, Value>,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            let param = params_to_bind.iter().find(|p| &p.name == name);
            if param.is_none() {
                bail_semantic!("unknown argument {}", name);
            }
            let val = if let Some(Type::DynTrait(trait_name)) = param.and_then(|p| p.ty.as_ref()) {
                Value::TraitObject {
                    trait_name: trait_name.clone(),
                    inner: Box::new(val),
                }
            } else {
                val
            };
            if let Some(Type::Simple(type_name)) = param.and_then(|p| p.ty.as_ref()) {
                if is_unit_type(type_name) {
                    if let Err(e) = validate_unit_type(&val, type_name) {
                        bail_semantic!("parameter '{}': {}", name, e);
                    }
                }
            }
            bound.insert(name.clone(), val);
        } else {
            if positional_idx >= params_to_bind.len() {
                bail_semantic!("too many arguments");
            }
            let param = params_to_bind[positional_idx];
            let val = if let Some(Type::DynTrait(trait_name)) = &param.ty {
                Value::TraitObject {
                    trait_name: trait_name.clone(),
                    inner: Box::new(val),
                }
            } else {
                val
            };
            if let Some(Type::Simple(type_name)) = &param.ty {
                if is_unit_type(type_name) {
                    if let Err(e) = validate_unit_type(&val, type_name) {
                        bail_semantic!("parameter '{}': {}", param.name, e);
                    }
                }
            }
            bound.insert(param.name.clone(), val);
            positional_idx += 1;
        }
    }

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                let v = if let Some(Type::DynTrait(trait_name)) = &param.ty {
                    Value::TraitObject {
                        trait_name: trait_name.clone(),
                        inner: Box::new(v),
                    }
                } else {
                    v
                };
                if let Some(Type::Simple(type_name)) = &param.ty {
                    if is_unit_type(type_name) {
                        if let Err(e) = validate_unit_type(&v, type_name) {
                            bail_semantic!("parameter '{}' default value: {}", param.name, e);
                        }
                    }
                }
                bound.insert(param.name.clone(), v);
            } else if let Some(injected_val) = injected.get(&param.name) {
                bound.insert(param.name.clone(), injected_val.clone());
            } else {
                bail_semantic!("missing argument {}", param.name);
            }
        }
    }

    Ok(bound)
}

fn bind_args_with_values(
    params: &[Parameter],
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    if args.len() > params_to_bind.len() {
        bail_semantic!("too many arguments");
    }

    let mut bound = HashMap::new();
    for (idx, param) in params_to_bind.iter().enumerate() {
        let value = if idx < args.len() {
            args[idx].clone()
        } else if let Some(default_expr) = &param.default {
            evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?
        } else {
            bail_semantic!("missing argument {}", param.name);
        };

        let value = if let Some(Type::DynTrait(trait_name)) = &param.ty {
            Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: Box::new(value),
            }
        } else {
            value
        };

        if let Some(Type::Simple(type_name)) = &param.ty {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type(&value, type_name) {
                    bail_semantic!("parameter '{}': {}", param.name, e);
                }
            }
        }
        bound.insert(param.name.clone(), value);
    }

    Ok(bound)
}

pub(crate) fn exec_lambda(
    params: &[String],
    body: &simple_parser::ast::Expr,
    args: &[Argument],
    call_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use simple_parser::ast::Expr;
    use super::block_execution::exec_block_closure;

    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                bail_semantic!("too many arguments to lambda");
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
        return exec_block_closure(nodes, &local_env, functions, classes, enums, impl_methods);
    }

    evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
}

pub(crate) fn exec_function(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    crate::effects::check_call_compatibility(&func.name, &func.effects)?;

    with_effect_context(&func.effects, || {
        exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx)
    })
}

pub(crate) fn exec_function_with_values(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    crate::effects::check_call_compatibility(&func.name, &func.effects)?;

    with_effect_context(&func.effects, || {
        exec_function_with_values_inner(func, args, outer_env, functions, classes, enums, impl_methods)
    })
}

pub(crate) fn exec_function_with_captured_env(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    crate::effects::check_call_compatibility(&func.name, &func.effects)?;

    with_effect_context(&func.effects, || {
        let mut local_env = captured_env.clone();

        let self_mode = SelfMode::IncludeSelf;
        let bound_args = bind_args(&func.params, args, outer_env, functions, classes, enums, impl_methods, self_mode)?;
        for (name, value) in bound_args {
            local_env.insert(name, value);
        }

        let result_value = exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods);
        let result = match result_value {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(e) => return Err(e),
        };

        if let Some(Type::Simple(type_name)) = &func.return_type {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type(&result, type_name) {
                    bail_semantic!("return type mismatch in '{}': {}", func.name, e);
                }
            }
        }

        Ok(result)
    })
}

fn exec_function_inner(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

    let mut local_env = Env::new();

    if let Some((class_name, fields)) = self_ctx {
        local_env.insert(
            "self".into(),
            Value::Object {
                class: class_name.to_string(),
                fields: fields.clone(),
            },
        );
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
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    if let Some(Type::Simple(type_name)) = &func.return_type {
        if is_unit_type(type_name) {
            if let Err(e) = validate_unit_type(&result, type_name) {
                bail_semantic!("return type mismatch in '{}': {}", func.name, e);
            }
        }
    }

    Ok(result)
}

fn exec_function_with_values_inner(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
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
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    if let Some(Type::Simple(type_name)) = &func.return_type {
        if is_unit_type(type_name) {
            if let Err(e) = validate_unit_type(&result, type_name) {
                bail_semantic!("return type mismatch in '{}': {}", func.name, e);
            }
        }
    }

    Ok(result)
}

pub(crate) fn instantiate_class(
    class_name: &str,
    args: &[Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let class_def = classes.get(class_name).ok_or_else(|| {
        semantic_err!("unknown class: {}", class_name)
    })?;

    let mut fields: HashMap<String, Value> = HashMap::new();
    for field in &class_def.fields {
        let val = if let Some(default_expr) = &field.default {
            evaluate_expr(default_expr, env, functions, classes, enums, impl_methods)?
        } else {
            Value::Nil
        };
        fields.insert(field.name.clone(), val);
    }

    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == METHOD_NEW) {
        let self_val = Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        };

        let mut local_env = env.clone();
        local_env.insert(METHOD_SELF.to_string(), self_val);

        for (k, v) in &fields {
            local_env.insert(k.clone(), v.clone());
        }

        let self_mode = SelfMode::SkipSelf;
        let injected = if has_inject_attr(new_method) {
            resolve_injected_args(
                &new_method.params,
                args,
                class_name,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                self_mode,
            )?
        } else {
            HashMap::new()
        };
        let bound = bind_args_with_injected(
            &new_method.params,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            self_mode,
            &injected,
        )?;
        for (name, val) in bound {
            local_env.insert(name, val);
        }

        match exec_block(&new_method.body, &mut local_env, functions, classes, enums, impl_methods) {
            Ok(Control::Return(v)) => Ok(v),
            Ok(_) => {
                Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields,
                }))
            }
            Err(CompileError::TryError(val)) => Ok(val),
            Err(e) => Err(e),
        }
    } else {
        let mut positional_idx = 0;
        for arg in args {
            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
            if let Some(name) = &arg.name {
                if !fields.contains_key(name) {
                    bail_semantic!("unknown field {} for class {}", name, class_name);
                }
                fields.insert(name.clone(), val);
            } else {
                if positional_idx < class_def.fields.len() {
                    let field_name = &class_def.fields[positional_idx].name;
                    fields.insert(field_name.clone(), val);
                    positional_idx += 1;
                } else {
                    bail_semantic!("too many arguments for class {}", class_name);
                }
            }
        }

        Ok(Value::Object {
            class: class_name.to_string(),
            fields,
        })
    }
}

fn has_inject_attr(method: &FunctionDef) -> bool {
    method
        .attributes
        .iter()
        .any(|attr| attr.name == "inject" || attr.name == "sys_inject")
}

fn resolve_injected_args(
    params: &[Parameter],
    args: &[Argument],
    class_name: &str,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    use crate::di::create_di_match_context;

    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    let mut provided_names = HashSet::new();
    let mut positional_count = 0usize;
    for arg in args {
        if let Some(name) = &arg.name {
            provided_names.insert(name.clone());
        } else {
            positional_count += 1;
        }
    }

    let mut injected = HashMap::new();
    for (idx, param) in params_to_bind.iter().enumerate() {
        if provided_names.contains(&param.name) {
            continue;
        }
        if idx < positional_count {
            continue;
        }
        let type_name = param_type_name(param).ok_or_else(|| {
            semantic_err!("injectable parameter '{}' missing type", param.name)
        })?;
        let di_config = get_di_config().ok_or_else(|| {
            semantic_err!("missing di config for injectable parameter '{}'", param.name)
        })?;
        let ctx = create_di_match_context(&type_name, class_name, &[]);
        let binding = di_config
            .select_binding("default", &ctx)
            .map_err(|_| semantic_err!("ambiguous DI binding for '{}'", type_name))?
            .ok_or_else(|| semantic_err!("no DI binding for '{}'", type_name))?;

        let value = resolve_binding_instance(
            &binding.impl_type,
            binding.scope,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?;
        injected.insert(param.name.clone(), value);
    }

    Ok(injected)
}

fn param_type_name(param: &Parameter) -> Option<String> {
    match param.ty.as_ref()? {
        Type::Simple(name) => Some(name.clone()),
        Type::Generic { name, .. } => Some(name.clone()),
        Type::DynTrait(name) => Some(name.clone()),
        Type::Optional(inner) => match inner.as_ref() {
            Type::Simple(name) => Some(name.clone()),
            Type::Generic { name, .. } => Some(name.clone()),
            Type::DynTrait(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn resolve_binding_instance(
    impl_type: &str,
    scope: DiScope,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if scope == DiScope::Singleton {
        if let Some(cached) = DI_SINGLETONS.with(|cell| cell.borrow().get(impl_type).cloned()) {
            return Ok(cached);
        }
    }

    let instance = if classes.contains_key(impl_type) {
        if let Some(aop_config) = get_aop_config() {
            let class_def = classes.get(impl_type).ok_or_else(|| {
                semantic_err!("unknown class: {}", impl_type)
            })?;
            let around = collect_runtime_init_advices(impl_type, class_def, &aop_config);
            if around.is_empty() {
                instantiate_class(
                    impl_type,
                    &[],
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?
            } else {
                let ctx = Arc::new(ProceedContext {
                    env: Arc::new(env.clone()),
                    functions: Arc::new(functions.clone()),
                    classes: Arc::new(classes.clone()),
                    enums: Arc::new(enums.clone()),
                    impl_methods: Arc::new(impl_methods.clone()),
                });
                invoke_runtime_around_chain(
                    Arc::new(around),
                    0,
                    impl_type,
                    ctx,
                )?
            }
        } else {
            instantiate_class(
                impl_type,
                &[],
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
        }
    } else {
        bail_semantic!("DI binding impl '{}' is not a class", impl_type);
    };

    if scope == DiScope::Singleton {
        DI_SINGLETONS.with(|cell| {
            cell.borrow_mut().insert(impl_type.to_string(), instance.clone());
        });
    }

    Ok(instance)
}

pub(crate) struct ProceedContext {
    pub(super) env: Arc<Env>,
    pub(super) functions: Arc<HashMap<String, FunctionDef>>,
    pub(super) classes: Arc<HashMap<String, ClassDef>>,
    pub(super) enums: Arc<Enums>,
    pub(super) impl_methods: Arc<ImplMethods>,
}

fn collect_runtime_init_advices(
    impl_type: &str,
    class_def: &ClassDef,
    aop_config: &AopConfig,
) -> Vec<crate::aop_config::AopAroundRule> {
    if !aop_config.runtime_enabled {
        return Vec::new();
    }
    let attrs: Vec<String> = class_def.attributes.iter().map(|attr| attr.name.clone()).collect();
    let ctx = crate::aop_config::create_aop_match_context(impl_type, impl_type, &attrs);
    let mut matches: Vec<_> = aop_config
        .around
        .iter()
        .filter(|rule| rule.predicate.matches(&ctx))
        .collect();
    if matches.is_empty() {
        return Vec::new();
    }
    matches.sort_by(|a, b| {
        let a_spec = a.predicate.specificity();
        let b_spec = b.predicate.specificity();
        b.priority
            .cmp(&a.priority)
            .then_with(|| b_spec.cmp(&a_spec))
            .then_with(|| a.order.cmp(&b.order))
    });
    matches.into_iter().cloned().collect()
}

fn invoke_runtime_around_chain(
    advices: Arc<Vec<crate::aop_config::AopAroundRule>>,
    idx: usize,
    impl_type: &str,
    ctx: Arc<ProceedContext>,
) -> Result<Value, CompileError> {
    if idx >= advices.len() {
        return instantiate_class(
            impl_type,
            &[],
            ctx.env.as_ref(),
            ctx.functions.as_ref(),
            ctx.classes.as_ref(),
            ctx.enums.as_ref(),
            ctx.impl_methods.as_ref(),
        );
    }

    let advice = &advices[idx];
    let func = ctx
        .functions
        .get(&advice.advice)
        .ok_or_else(|| semantic_err!("around advice '{}' not found", advice.advice))?;

    let called = Arc::new(AtomicBool::new(false));
    let called_marker = Arc::clone(&called);
    let advices_clone = Arc::clone(&advices);
    let impl_name = impl_type.to_string();
    let next_idx = idx + 1;
    let ctx_clone = Arc::clone(&ctx);

    let proceed = Value::NativeFunction(NativeFunction {
        name: "proceed".to_string(),
        func: Arc::new(move |args: &[Value]| {
            if !args.is_empty() {
                return Err(CompileError::Semantic(
                    "proceed() takes no arguments".to_string(),
                ));
            }
            if called_marker.swap(true, std::sync::atomic::Ordering::SeqCst) {
                return Err(CompileError::Semantic(
                    "around advice called proceed() more than once".to_string(),
                ));
            }
            invoke_runtime_around_chain(
                Arc::clone(&advices_clone),
                next_idx,
                &impl_name,
                Arc::clone(&ctx_clone),
            )
        }),
    });

    let result = exec_function_with_values(
        func,
        &[proceed],
        ctx.env.as_ref(),
        ctx.functions.as_ref(),
        ctx.classes.as_ref(),
        ctx.enums.as_ref(),
        ctx.impl_methods.as_ref(),
    )?;

    if !called.load(std::sync::atomic::Ordering::SeqCst) {
        return Err(CompileError::Semantic(
            "around advice did not call proceed() exactly once".to_string(),
        ));
    }

    Ok(result)
}
