// Core function execution for interpreter
// Function binding, lambda execution, function call logic

//==============================================================================
// Helper Macros for Reducing Duplication
//==============================================================================

/// Wrap value in TraitObject if parameter has DynTrait type
macro_rules! wrap_trait_object {
    ($val:expr, $param_ty:expr) => {
        if let Some(Type::DynTrait(trait_name)) = $param_ty {
            Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: Box::new($val),
            }
        } else {
            $val
        }
    };
}

/// Validate unit type for parameter or return type
macro_rules! validate_unit {
    ($val:expr, $ty:expr, $context:expr) => {
        if let Some(Type::Simple(type_name)) = $ty {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type($val, type_name) {
                    bail_semantic!("{}: {}", $context, e);
                }
            }
        }
    };
}

/// Check effect compatibility and execute with effect context
macro_rules! with_effect_check {
    ($func:expr, $body:expr) => {{
        crate::effects::check_call_compatibility(&$func.name, &$func.effects)?;
        with_effect_context(&$func.effects, || $body)
    }};
}

/// Extract result from exec_block_fn return value
macro_rules! extract_block_result {
    ($block_exec:expr) => {
        match $block_exec {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(CompileError::TryError(val)) => val,
            Err(e) => return Err(e),
        }
    };
}

use crate::aop_config::AopConfig;
use crate::di::DiScope;
use crate::error::CompileError;
use crate::interpreter::{
    evaluate_expr, exec_block, exec_block_fn, get_aop_config, get_di_config, with_effect_context, Control,
    DI_SINGLETONS,
};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;

// Diagram tracing for call flow profiling
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef, Parameter, SelfMode, Type};
use simple_runtime::value::diagram_ffi;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

type Enums = HashMap<String, EnumDef>;

// Thread-local to track classes currently executing their `new` method.
// This prevents infinite recursion when `new` method calls `ClassName(args)` internally.
thread_local! {
    pub(crate) static IN_NEW_METHOD: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";
const METHOD_NEW: &str = "new";

pub(crate) fn bind_args(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
    injected: &HashMap<String, Value>,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    // Check if there's a variadic parameter (should be last)
    let variadic_param_idx = params_to_bind.iter().position(|p| p.variadic);

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    let mut variadic_values = Vec::new();

    for arg in args {
        // Check if this is a spread expression (args...)
        if let Expr::Spread(inner) = &arg.value {
            // Evaluate the inner expression (should be variadic/array/tuple)
            let spread_val = evaluate_expr(inner, &mut outer_env, functions, classes, enums, impl_methods)?;

            // Extract values from spread
            let spread_values: Vec<Value> = match spread_val {
                Value::Array(arr) => arr,
                Value::Tuple(tup) => tup,
                _ => {
                    bail_semantic!("spread operator requires array or tuple value");
                }
            };

            // Bind each spread value to the next positional parameter
            for spread_item in spread_values {
                if let Some(var_idx) = variadic_param_idx {
                    if positional_idx == var_idx {
                        // This value goes into variadic parameter
                        variadic_values.push(spread_item);
                    } else if positional_idx < var_idx {
                        // Regular parameter before variadic
                        let param = params_to_bind[positional_idx];
                        let val = wrap_trait_object!(spread_item, param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    } else {
                        bail_semantic!("too many arguments");
                    }
                } else {
                    // No variadic - bind to regular parameters
                    if positional_idx >= params_to_bind.len() {
                        bail_semantic!("too many arguments");
                    }
                    let param = params_to_bind[positional_idx];
                    let val = wrap_trait_object!(spread_item, param.ty.as_ref());
                    validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                    bound.insert(param.name.clone(), val);
                }
                positional_idx += 1;
            }
        } else {
            // Normal argument (not spread)
            let val = evaluate_expr(&arg.value, &mut outer_env, functions, classes, enums, impl_methods)?;

            if let Some(name) = &arg.name {
                // Named argument
                let param = params_to_bind.iter().find(|p| &p.name == name);
                if param.is_none() {
                    bail_semantic!("unknown argument {}", name);
                }
                let val = wrap_trait_object!(val, param.and_then(|p| p.ty.as_ref()));
                validate_unit!(&val, param.and_then(|p| p.ty.as_ref()), format!("parameter '{}'", name));
                bound.insert(name.clone(), val);
            } else {
                // Positional argument
                if let Some(var_idx) = variadic_param_idx {
                    if positional_idx >= var_idx {
                        // This and all remaining positional args go into variadic parameter
                        variadic_values.push(val);
                    } else {
                        // Regular positional parameter before variadic
                        let param = params_to_bind[positional_idx];
                        let val = wrap_trait_object!(val, param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    }
                } else {
                    // No variadic parameter - normal positional binding
                    if positional_idx >= params_to_bind.len() {
                        bail_semantic!("too many arguments");
                    }
                    let param = params_to_bind[positional_idx];
                    let val = wrap_trait_object!(val, param.ty.as_ref());
                    validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                    bound.insert(param.name.clone(), val);
                }
                positional_idx += 1;
            }
        }
    }

    // Bind variadic parameter with collected values
    if let Some(var_idx) = variadic_param_idx {
        let param = params_to_bind[var_idx];
        bound.insert(param.name.clone(), Value::Tuple(variadic_values));
    }

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, &mut outer_env, functions, classes, enums, impl_methods)?;
                let v = wrap_trait_object!(v, param.ty.as_ref());
                validate_unit!(
                    &v,
                    param.ty.as_ref(),
                    format!("parameter '{}' default value", param.name)
                );
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
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
            evaluate_expr(default_expr, &mut outer_env, functions, classes, enums, impl_methods)?
        } else {
            bail_semantic!("missing argument {}", param.name);
        };

        let value = wrap_trait_object!(value, param.ty.as_ref());
        validate_unit!(&value, param.ty.as_ref(), format!("parameter '{}'", param.name));
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::block_execution::exec_block_closure;
    use simple_parser::ast::Expr;

    // Diagram tracing for lambda execution
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call("<lambda>");
    }

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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx)
    })
}

pub(crate) fn exec_function_with_values(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_with_values_inner(func, args, &mut outer_env, functions, classes, enums, impl_methods)
    })
}

/// Execute function with already-evaluated Values and self context for method calls
pub(crate) fn exec_function_with_values_and_self(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
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
                // For class methods, self is an Object
                local_env.insert(
                    "self".into(),
                    Value::Object {
                        class: class_name.to_string(),
                        fields: fields.clone(),
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
        for (name, val) in bound {
            local_env.insert(name, val);
        }

        let result = extract_block_result!(exec_block_fn(
            &func.body,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods
        ));
        validate_unit!(
            &result,
            func.return_type.as_ref(),
            format!("return type mismatch in '{}'", func.name)
        );

        Ok(result)
    })
}

pub(crate) fn exec_function_with_captured_env(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    captured_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
        for (name, value) in bound_args {
            local_env.insert(name, value);
        }

        let result = extract_block_result!(exec_block_fn(
            &func.body,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods
        ));
        validate_unit!(
            &result,
            func.return_type.as_ref(),
            format!("return type mismatch in '{}'", func.name)
        );

        Ok(result)
    })
}

fn exec_function_inner(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    // Layout recording for 4KB page locality optimization
    crate::layout_recorder::record_function_call(&func.name);

    // Diagram tracing for call flow profiling
    if diagram_ffi::is_diagram_enabled() {
        if let Some((class_name, _)) = self_ctx {
            // Method call on a class
            diagram_ffi::trace_method(class_name, &func.name);
        } else {
            // Free function call
            diagram_ffi::trace_call(&func.name);
        }
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
            local_env.insert("self".into(), fields.get("self").unwrap().clone());
        } else {
            // For class methods, self is an Object
            local_env.insert(
                "self".into(),
                Value::Object {
                    class: class_name.to_string(),
                    fields: fields.clone(),
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
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = extract_block_result!(exec_block_fn(
        &func.body,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods
    ));
    validate_unit!(
        &result,
        func.return_type.as_ref(),
        format!("return type mismatch in '{}'", func.name)
    );

    // Record function return for layout call graph tracking
    crate::layout_recorder::record_function_return();

    Ok(result)
}

fn exec_function_with_values_inner(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Layout recording for 4KB page locality optimization
    crate::layout_recorder::record_function_call(&func.name);

    // Diagram tracing for call flow profiling
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call(&func.name);
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
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = extract_block_result!(exec_block_fn(
        &func.body,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods
    ));
    validate_unit!(
        &result,
        func.return_type.as_ref(),
        format!("return type mismatch in '{}'", func.name)
    );

    // Record function return for layout call graph tracking
    crate::layout_recorder::record_function_return();

    Ok(result)
}

pub(crate) fn instantiate_class(
    class_name: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for class instantiation
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_method(class_name, "new");
    }

    let class_def = classes
        .get(class_name)
        .cloned()
        .ok_or_else(|| semantic_err!("unknown class: {}", class_name))?;

    let mut fields: HashMap<String, Value> = HashMap::new();
    for field in &class_def.fields {
        let val = if let Some(default_expr) = &field.default {
            evaluate_expr(default_expr, env, functions, classes, enums, impl_methods)?
        } else {
            Value::Nil
        };
        fields.insert(field.name.clone(), val);
    }

    // Check if we should call the `new` method
    // Only call `new()` if it has special attributes like #[inject]
    // Otherwise, do field-based construction
    let already_in_new = IN_NEW_METHOD.with(|set| set.borrow().contains(class_name));

    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == METHOD_NEW) {
        // Only auto-call new() if it has special attributes like #[inject]
        // Otherwise, use field-based construction
        let should_call_new = has_inject_attr(new_method);

        if should_call_new && !already_in_new {
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

            // Mark this class as currently in its `new` method
            IN_NEW_METHOD.with(|set| set.borrow_mut().insert(class_name.to_string()));

            let result = match exec_block(
                &new_method.body,
                &mut local_env,
                functions,
                classes,
                enums,
                impl_methods,
            ) {
                Ok(Control::Return(v)) => Ok(v),
                Ok(_) => Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields,
                })),
                Err(CompileError::TryError(val)) => Ok(val),
                Err(e) => Err(e),
            };

            // Remove from tracking set
            IN_NEW_METHOD.with(|set| set.borrow_mut().remove(class_name));

            return result;
        }
    }

    // Field-based construction
    // Used when there's no `new` method with special attributes
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

fn resolve_binding_instance(
    impl_type: &str,
    scope: DiScope,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
        let mut functions_clone = (*ctx.functions).clone();
        let mut classes_clone = (*ctx.classes).clone();
        return instantiate_class(
            impl_type,
            &[],
            ctx.env.as_ref(),
            &mut functions_clone,
            &mut classes_clone,
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
                return Err(CompileError::Semantic("proceed() takes no arguments".to_string()));
            }
            if called_marker.swap(true, std::sync::atomic::Ordering::SeqCst) {
                return Err(CompileError::Semantic(
                    "around advice called proceed() more than once".to_string(),
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
        ctx.env.as_ref(),
        &mut functions_clone,
        &mut classes_clone,
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
