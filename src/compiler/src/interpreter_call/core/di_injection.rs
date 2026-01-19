// Dependency injection resolution

use super::class_instantiation::instantiate_class;
use crate::di::DiScope;
use crate::error::CompileError;
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
        let type_name = param_type_name(param)
            .ok_or_else(|| semantic_err!("injectable parameter '{}' missing type", param.name))?;
        let di_config = get_di_config()
            .ok_or_else(|| semantic_err!("missing di config for injectable parameter '{}'", param.name))?;
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
            let class_def = classes
                .get(impl_type)
                .ok_or_else(|| semantic_err!("unknown class: {}", impl_type))?;
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
        bail_semantic!("DI binding impl '{}' is not a class", impl_type);
    };

    if scope == DiScope::Singleton {
        DI_SINGLETONS.with(|cell| {
            cell.borrow_mut().insert(impl_type.to_string(), instance.clone());
        });
    }

    Ok(instance)
}
