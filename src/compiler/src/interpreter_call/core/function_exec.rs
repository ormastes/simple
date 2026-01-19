// Core function execution logic

use super::arg_binding::{bind_args, bind_args_with_values};
use super::async_support::{is_async_function, wrap_in_promise};
use super::macros::*;
use crate::error::CompileError;
use crate::interpreter::{exec_block_fn, Control};
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef, SelfMode, Type};
use simple_runtime::value::diagram_ffi;
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

pub(crate) fn exec_function(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
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
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_check!(func, {
        exec_function_with_values_inner(func, args, outer_env, functions, classes, enums, impl_methods)
    })
}

/// Execute function with already-evaluated Values and self context for method calls
pub(crate) fn exec_function_with_values_and_self(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &mut Env,
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
    outer_env: &mut Env,
    captured_env: &mut Env,
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
    outer_env: &mut Env,
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
            let self_val = fields.get("self").unwrap().clone();
            local_env.insert("self".into(), self_val);
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

    // Wrap result in Promise for async functions (async fn returns Promise<T>)
    let result = if is_async_function(func) {
        wrap_in_promise(result)
    } else {
        result
    };

    Ok(result)
}

fn exec_function_with_values_inner(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &mut Env,
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

    // Wrap result in Promise for async functions (async fn returns Promise<T>)
    let result = if is_async_function(func) {
        wrap_in_promise(result)
    } else {
        result
    };

    Ok(result)
}
