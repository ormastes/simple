//! Dependency injection support for function calls

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, atomic::AtomicBool};
use simple_parser::ast::{Argument, Parameter, Type};
use crate::value::Value;
use crate::{ClassDef, CompileError, Enums, FunctionDef, ImplMethods};
use crate::interpreter::env::Env;
use crate::interpreter::METHOD_SELF;
use crate::interpreter::DI_SINGLETONS;
use crate::{bail_semantic, semantic_err};
use crate::di::get_di_config;
use crate::aop_config::get_aop_config;

use super::execution::*;

pub(super) fn has_inject_attr(method: &FunctionDef) -> bool {
    method
        .attributes
        .iter()
        .any(|attr| attr.name == "inject" || attr.name == "sys_inject")
}

pub(super) fn resolve_injected_args(
    params: &[Parameter],
    args: &[Argument],
    class_name: &str,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: simple_parser::ast::SelfMode,
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

pub(super) fn param_type_name(param: &Parameter) -> Option<String> {
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

pub(super) fn resolve_binding_instance(
    impl_type: &str,
    scope: crate::di::DiScope,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if scope == crate::di::DiScope::Singleton {
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

    if scope == crate::di::DiScope::Singleton {
        DI_SINGLETONS.with(|cell| {
            cell.borrow_mut().insert(impl_type.to_string(), instance.clone());
        });
    }

    Ok(instance)
}

pub(super) struct ProceedContext {
    pub env: Arc<Env>,
    pub functions: Arc<HashMap<String, FunctionDef>>,
    pub classes: Arc<HashMap<String, ClassDef>>,
    pub enums: Arc<Enums>,
    pub impl_methods: Arc<ImplMethods>,
}

pub(super) fn collect_runtime_init_advices(
    impl_type: &str,
    class_def: &ClassDef,
    aop_config: &crate::aop_config::AopConfig,
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

pub(super) fn invoke_runtime_around_chain(
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

    let proceed = Value::NativeFunction(crate::value::NativeFunction {
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
