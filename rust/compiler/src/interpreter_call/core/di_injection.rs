// Dependency injection resolution

use super::class_instantiation::instantiate_class;
use crate::di::DiScope;
use crate::error::{CompileError, ErrorContext, codes, typo};
use crate::interpreter::{get_di_config, DI_SINGLETONS};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef, Parameter, SelfMode, Type};
use std::collections::{HashMap, HashSet};

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";

pub(crate) fn resolve_injected_args(
    params: &[Parameter],
    args: &[Argument],
    class_name: &str,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_SELF_PARAM)
                .with_help("injectable parameters must have a type annotation");
            CompileError::semantic_with_context(
                format!("injectable parameter '{}' is missing type annotation", param.name),
                ctx,
            )
        })?;
        let di_config = get_di_config().ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("ensure DI configuration is properly initialized");
            CompileError::semantic_with_context(
                format!("DI configuration not found for injectable parameter '{}'", param.name),
                ctx,
            )
        })?;
        let ctx = create_di_match_context(&type_name, class_name, &[]);
        let binding = di_config
            .select_binding("default", &ctx)
            .map_err(|_| {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ATTRIBUTE_POSITION)
                    .with_help("check that exactly one DI binding is configured for this type");
                CompileError::semantic_with_context(format!("ambiguous DI binding found for type '{}'", type_name), ctx)
            })?
            .ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNSUPPORTED_FEATURE)
                    .with_help("ensure a DI binding is configured for this type");
                CompileError::semantic_with_context(format!("no DI binding configured for type '{}'", type_name), ctx)
            })?;

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

pub(crate) fn resolve_binding_instance(
    impl_type: &str,
    scope: DiScope,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::aop_advice::{collect_runtime_init_advices, invoke_runtime_around_chain, ProceedContext};
    use crate::interpreter::get_aop_config;
    use std::sync::Arc;

    if scope == DiScope::Singleton {
        if let Some(cached) = DI_SINGLETONS.with(|cell| cell.borrow().get(impl_type).cloned()) {
            return Ok(cached);
        }
    }

    let instance = if classes.contains_key(impl_type) {
        if let Some(aop_config) = get_aop_config() {
            let class_def = classes.get(impl_type).ok_or_else(|| {
                let available_classes: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
                let suggestion = if !available_classes.is_empty() {
                    typo::suggest_name(impl_type, available_classes.clone())
                } else {
                    None
                };

                let mut ctx = ErrorContext::new()
                    .with_code(codes::UNKNOWN_CLASS)
                    .with_help("check that the class is defined or imported in this scope");

                if let Some(best_match) = suggestion {
                    ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                }

                CompileError::semantic_with_context(format!("class `{}` not found in this scope", impl_type), ctx)
            })?;
            let around = collect_runtime_init_advices(impl_type, class_def, &aop_config);
            if around.is_empty() {
                instantiate_class(impl_type, &[], env, functions, classes, enums, impl_methods)?
            } else {
                let ctx = Arc::new(ProceedContext {
                    env: Arc::new(env.clone()),
                    functions: Arc::new(functions.clone()),
                    classes: Arc::new(classes.clone()),
                    enums: Arc::new(enums.clone()),
                    impl_methods: Arc::new(impl_methods.clone()),
                });
                invoke_runtime_around_chain(Arc::new(around), 0, impl_type, ctx)?
            }
        } else {
            instantiate_class(impl_type, &[], env, functions, classes, enums, impl_methods)?
        }
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_CLASS)
            .with_help("DI bindings must reference a class type");
        return Err(CompileError::semantic_with_context(
            format!("DI binding impl '{}' is not a class", impl_type),
            ctx,
        ));
    };

    if scope == DiScope::Singleton {
        DI_SINGLETONS.with(|cell| {
            cell.borrow_mut().insert(impl_type.to_string(), instance.clone());
        });
    }

    Ok(instance)
}
