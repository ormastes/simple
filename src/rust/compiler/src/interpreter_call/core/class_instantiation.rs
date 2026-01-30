// Class instantiation and initialization support

use super::arg_binding::bind_args_with_injected;
use super::di_injection::resolve_injected_args;
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::interpreter::{evaluate_expr, exec_block};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef, SelfMode};
use simple_runtime::value::diagram_ffi;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";
const METHOD_NEW: &str = "new";
const METHOD_INIT: &str = "__init__";

// Thread-local to track classes currently executing their `new` method.
// This prevents infinite recursion when `new` method calls `ClassName(args)` internally.
thread_local! {
    pub(crate) static IN_NEW_METHOD: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

pub(crate) fn instantiate_class(
    class_name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for class instantiation
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_method(class_name, "new");
    }

    let class_def = classes.get(class_name).cloned().ok_or_else(|| {
        let available_classes: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
        let suggestion = if !available_classes.is_empty() {
            typo::suggest_name(class_name, available_classes.clone())
        } else {
            None
        };

        let mut ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_CLASS)
            .with_help("check that the class is defined or imported in this scope");

        if let Some(best_match) = suggestion {
            ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
        }

        CompileError::semantic_with_context(format!("class `{}` not found in this scope", class_name), ctx)
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

    // Check if we should call the `new` method
    // Only call `new()` if it has special attributes like #[inject]
    // Otherwise, do field-based construction
    let already_in_new = IN_NEW_METHOD.with(|set| set.borrow().contains(class_name));

    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == METHOD_NEW) {
        // Auto-call new() for Python-style construction: ClassName() calls ClassName.new()
        // Skip if we're already inside new() to prevent infinite recursion
        //
        // Call new() if:
        // 1. Exact arg count match, OR
        // 2. Has #[inject] attribute (missing args will be injected via DI)
        let new_param_count = new_method.params.len();
        let has_inject = has_inject_attr(new_method);
        let should_call_new = args.len() == new_param_count || has_inject;

        if should_call_new && !already_in_new {
            let self_val = Value::Object {
                class: class_name.to_string(),
                fields: Arc::new(fields.clone()),
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
                Ok(crate::interpreter::Control::Return(v)) => Ok(v),
                Ok(_) => Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields: Arc::new(fields),
                })),
                Err(CompileError::TryError(val)) => Ok(val),
                Err(e) => Err(e),
            };

            // Remove from tracking set
            IN_NEW_METHOD.with(|set| set.borrow_mut().remove(class_name));

            return result;
        }
    }

    // Check if class has __init__ method for Python-style initialization
    if let Some(init_method) = class_def.methods.iter().find(|m| m.name == METHOD_INIT) {
        // Create the object with default field values first
        let self_val = Value::Object {
            class: class_name.to_string(),
            fields: Arc::new(fields.clone()),
        };

        // Set up local environment for __init__
        let mut local_env = env.clone();
        local_env.insert(METHOD_SELF.to_string(), self_val);

        // Bind arguments to __init__ parameters (skipping self)
        let self_mode = SelfMode::SkipSelf;
        let bound = super::arg_binding::bind_args(
            &init_method.params,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            self_mode,
        )?;
        for (name, val) in bound {
            local_env.insert(name, val);
        }

        // Execute __init__ body
        match exec_block(
            &init_method.body,
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
        ) {
            Ok(_) | Err(CompileError::TryError(_)) => {}
            Err(e) => return Err(e),
        }

        // Return the modified self from local_env
        return Ok(local_env.get(METHOD_SELF).cloned().unwrap_or(Value::Object {
            class: class_name.to_string(),
            fields: Arc::new(fields),
        }));
    }

    // Field-based construction
    // Used when there's no `__init__` or `new` method with special attributes
    let mut positional_idx = 0;
    for arg in args {
        let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            if !fields.contains_key(name) {
                // E1012 - Undefined Field
                let available_fields: Vec<&str> = fields.keys().map(|s| s.as_str()).collect();
                let suggestion = if !available_fields.is_empty() {
                    typo::suggest_name(name, available_fields.clone())
                } else {
                    None
                };

                let mut ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_FIELD)
                    .with_help("check the field name and class definition");

                if let Some(best_match) = suggestion {
                    ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                }

                if !available_fields.is_empty() && available_fields.len() <= 5 {
                    let fields_list = available_fields.join(", ");
                    ctx = ctx.with_note(format!("available fields: {}", fields_list));
                }

                return Err(CompileError::semantic_with_context(
                    format!("class `{}` has no field named `{}`", class_name, name),
                    ctx,
                ));
            }
            fields.insert(name.clone(), val);
        } else {
            if positional_idx < class_def.fields.len() {
                let field_name = &class_def.fields[positional_idx].name;
                fields.insert(field_name.clone(), val);
                positional_idx += 1;
            } else {
                // E1023 - Invalid Struct Literal
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_STRUCT_LITERAL)
                    .with_help(format!(
                        "class `{}` expects {} field(s)",
                        class_name,
                        class_def.fields.len()
                    ))
                    .with_note(format!("provided {} positional argument(s)", args.len()));
                return Err(CompileError::semantic_with_context(
                    format!("too many arguments for class `{}` constructor", class_name),
                    ctx,
                ));
            }
        }
    }

    Ok(Value::Object {
        class: class_name.to_string(),
        fields: Arc::new(fields),
    })
}

fn has_inject_attr(method: &FunctionDef) -> bool {
    method
        .attributes
        .iter()
        .any(|attr| attr.name == "inject" || attr.name == "sys_inject")
}

/// Clear class instantiation thread-local state.
///
/// This should be called between test runs to prevent memory leaks.
pub fn clear_class_instantiation_state() {
    IN_NEW_METHOD.with(|cell| cell.borrow_mut().clear());
}
