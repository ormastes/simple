// Class instantiation and initialization support

use super::arg_binding::bind_args_with_injected;
use super::di_injection::resolve_injected_args;
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::interpreter::{evaluate_expr, exec_block, exec_block_fn};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef, SelfMode};
use simple_runtime::value::diagram_sffi;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

const METHOD_SELF: &str = "self";
const METHOD_NEW: &str = "new";
const METHOD_INIT: &str = "__init__";

// Thread-local to track classes currently executing their `new` method.
// This prevents infinite recursion when `new` method calls `ClassName(args)` internally.
thread_local! {
    pub(crate) static IN_NEW_METHOD: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

/// Whether a class definition can accept every named field in a construction.
/// Positional args are ignored here (they bind by position to the def's fields).
fn class_def_accepts_named_args(def: &ClassDef, args: &[Argument]) -> bool {
    args.iter().all(|a| match &a.name {
        Some(n) => def.fields.iter().any(|f| &f.name == n),
        None => true,
    })
}

/// Resolve a class construction to the definition whose fields fit the literal.
/// The flat class registry keeps only one def per bare name (last-write-wins); if
/// that def doesn't fit, consult CLASS_OVERLOADS for a same-named def that does.
/// Returns the primary def unchanged when it already fits (the common case).
fn pick_fitting_class_def(class_name: &str, primary: Arc<ClassDef>, args: &[Argument]) -> Arc<ClassDef> {
    if class_def_accepts_named_args(&primary, args) {
        return primary;
    }
    crate::interpreter::CLASS_OVERLOADS
        .with(|cell| {
            cell.borrow()
                .get(class_name)
                .and_then(|defs| defs.iter().find(|d| class_def_accepts_named_args(d, args)).cloned())
        })
        .unwrap_or(primary)
}

pub(crate) fn instantiate_class(
    class_name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for class instantiation
    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_method(class_name, "new");
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

    // Structural disambiguation across colliding type names. The interpreter's
    // flat class registry is keyed by bare name (last-write-wins), so two modules
    // that both define e.g. `struct CompileOptions` shadow each other. If the
    // registered def doesn't have all the fields this literal sets, pick a
    // same-named overload whose fields do. Only rescues constructions that would
    // otherwise fail, so it cannot change the result of an already-valid literal.
    let class_def = pick_fitting_class_def(class_name, class_def, args);
    if std::env::var("SIMPLE_DBG_COLLISION").is_ok() {
        eprintln!(
            "[DBG INST] call_name={} picked_def={} def_fields=[{}] args=[{}]",
            class_name,
            class_def.name,
            class_def
                .fields
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>()
                .join(","),
            args.iter().filter_map(|a| a.name.clone()).collect::<Vec<_>>().join(",")
        );
    }

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
        // 2. Has @inject / @sys_inject marker (missing args will be injected via DI)
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

            let result = match exec_block_fn(
                &new_method.body,
                &mut local_env,
                functions,
                classes,
                enums,
                impl_methods,
            ) {
                Ok((crate::interpreter::Control::Return(v), _)) => Ok(v),
                // Implicit return: a `new` whose body ends in a bare expression that
                // constructs its own type (e.g. `SymbolId(id: id)`) returns that value,
                // like any function — previously its value was discarded and the
                // default-field `self` returned instead (fields left nil). Restricted
                // to an own-class object so mutation-style `new` (ending in an
                // assignment or bare `self`) still returns the mutated `self`.
                Ok((
                    _,
                    Some(Value::Object {
                        class,
                        fields: obj_fields,
                    }),
                )) if class == class_name => Ok(Value::Object {
                    class,
                    fields: obj_fields,
                }),
                Ok((_, _)) => Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields: Arc::new(fields),
                })),
                Err(CompileError::TryError(val)) => Ok(*val),
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
    // Used when there's no `__init__` or `new` method with special attributes.
    //
    // First pass: apply struct spreads. Paren-form functional update
    // `Foo(..base, field: x)` copies every field of `base` before explicit
    // fields override them (identical semantics to the brace-form
    // `Expr::StructInit` spread handled in interpreter/expr/collections.rs).
    // The parser encodes the `..base` spread argument as an unnamed positional
    // prefix range `Expr::Range { start: None, end: Some(base) }` (the `..`
    // token is shared with range syntax), so recognize that shape here. Without
    // this the spread argument was evaluated as a real range and coerced via
    // `as_int()`, which failed with "type mismatch: cannot convert object to
    // int" whenever the base was a struct (e.g. `MirFunction(..func, blocks:
    // ...)` throughout the MIR optimization passes).
    for arg in args {
        if arg.name.is_some() {
            continue;
        }
        let base_expr = match &arg.value {
            simple_parser::ast::Expr::Range {
                start: None,
                end: Some(base),
                ..
            } => base,
            _ => continue,
        };
        let base_val = evaluate_expr(base_expr, env, functions, classes, enums, impl_methods)?;
        match &base_val {
            Value::Object {
                fields: base_fields, ..
            } => {
                for (k, v) in base_fields.as_ref() {
                    fields.insert(k.clone(), v.clone());
                }
            }
            Value::Dict(base_map) => {
                for (k, v) in base_map.iter() {
                    fields.insert(k.clone(), v.clone());
                }
            }
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("struct spread (..) requires an object or dict value as base");
                return Err(CompileError::semantic_with_context(
                    format!(
                        "type mismatch: struct spread requires object or dict, got {}",
                        base_val.type_name()
                    ),
                    ctx,
                ));
            }
        }
    }

    // Second pass: explicit named/positional fields override any spread values.
    let mut positional_idx = 0;
    for arg in args {
        // Struct-spread arguments were consumed in the first pass above.
        if arg.name.is_none()
            && matches!(
                &arg.value,
                simple_parser::ast::Expr::Range {
                    start: None,
                    end: Some(_),
                    ..
                }
            )
        {
            continue;
        }
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

                if std::env::var("SIMPLE_DBG_COLLISION").is_ok() {
                    eprintln!(
                        "[DBG CONSTRUCT-ERR] call_name={} picked_def={} missing_field={} def_fields=[{}]",
                        class_name,
                        class_def.name,
                        name,
                        class_def
                            .fields
                            .iter()
                            .map(|f| f.name.as_str())
                            .collect::<Vec<_>>()
                            .join(",")
                    );
                }
                return Err(CompileError::semantic_with_context(
                    format!("class `{}` has no field named `{}`", class_name, name),
                    ctx,
                ));
            }
            fields.insert(name.clone(), val);
        } else if positional_idx < class_def.fields.len() {
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

    Ok(Value::Object {
        class: class_name.to_string(),
        fields: Arc::new(fields),
    })
}

fn has_inject_attr(method: &FunctionDef) -> bool {
    let has_attribute = method
        .attributes
        .iter()
        .any(|attr| attr.name == "inject" || attr.name == "sys_inject");
    let has_decorator = method.decorators.iter().any(|decorator| match &decorator.name {
        simple_parser::ast::Expr::Identifier(name) => name == "inject" || name == "sys_inject",
        _ => false,
    });
    let has_param_inject = method.params.iter().any(|param| param.inject);

    has_attribute || has_decorator || has_param_inject
}

/// Clear class instantiation thread-local state.
///
/// This should be called between test runs to prevent memory leaks.
pub fn clear_class_instantiation_state() {
    IN_NEW_METHOD.with(|cell| cell.borrow_mut().clear());
}
