// AOP (Aspect-Oriented Programming) around advice support

use super::class_instantiation::instantiate_class;
use super::function_exec::exec_function_with_values;
use crate::aop_config::AopConfig;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::*;
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

pub(crate) struct ProceedContext {
    pub(super) env: Arc<Env>,
    pub(super) functions: Arc<HashMap<String, FunctionDef>>,
    pub(super) classes: Arc<HashMap<String, ClassDef>>,
    pub(super) enums: Arc<Enums>,
    pub(super) impl_methods: Arc<ImplMethods>,
}

pub(crate) fn collect_runtime_init_advices(
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

pub(crate) fn invoke_runtime_around_chain(
    advices: Arc<Vec<crate::aop_config::AopAroundRule>>,
    idx: usize,
    impl_type: &str,
    ctx: Arc<ProceedContext>,
) -> Result<Value, CompileError> {
    if idx >= advices.len() {
        let mut functions_clone = (*ctx.functions).clone();
        let mut classes_clone = (*ctx.classes).clone();
        return instantiate_class(
            impl_type,
            &[],
            &mut (*ctx.env).clone(),
            &mut functions_clone,
            &mut classes_clone,
            ctx.enums.as_ref(),
            ctx.impl_methods.as_ref(),
        );
    }

    let advice = &advices[idx];
    let func = ctx.functions.get(&advice.advice).ok_or_else(|| {
        let ctx_err = ErrorContext::new()
            .with_code(codes::INVALID_POINTCUT_SELECTOR)
            .with_help("ensure the advice function is defined and exported");
        CompileError::semantic_with_context(format!("around advice '{}' not found", advice.advice), ctx_err)
    })?;

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
                let ctx_err = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("proceed() does not accept any arguments");
                return Err(CompileError::semantic_with_context(
                    "proceed() takes no arguments".to_string(),
                    ctx_err,
                ));
            }
            if called_marker.swap(true, std::sync::atomic::Ordering::SeqCst) {
                let ctx_err = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("proceed() must be called exactly once in around advice");
                return Err(CompileError::semantic_with_context(
                    "around advice called proceed() more than once".to_string(),
                    ctx_err,
                ));
            }
            invoke_runtime_around_chain(Arc::clone(&advices_clone), next_idx, &impl_name, Arc::clone(&ctx_clone))
        }),
    });

    let mut functions_clone = (*ctx.functions).clone();
    let mut classes_clone = (*ctx.classes).clone();
    let result = exec_function_with_values(
        func,
        &[proceed],
        &mut (*ctx.env).clone(),
        &mut functions_clone,
        &mut classes_clone,
        ctx.enums.as_ref(),
        ctx.impl_methods.as_ref(),
    )?;

    if !called.load(std::sync::atomic::Ordering::SeqCst) {
        let ctx_err = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help("around advice must call proceed() exactly once");
        return Err(CompileError::semantic_with_context(
            "around advice did not call proceed() exactly once".to_string(),
            ctx_err,
        ));
    }

    Ok(result)
}
