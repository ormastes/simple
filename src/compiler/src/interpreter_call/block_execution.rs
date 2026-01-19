// Block closure execution helpers for interpreter_call module

use super::super::interpreter_helpers::handle_method_call_with_self_update;
use super::bdd::{BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_INDENT};
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{evaluate_expr, pattern_matches, EXTERN_FUNCTIONS, MODULE_GLOBALS};
use crate::value::*;
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Node};
use simple_runtime::value::diagram_ffi;
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

fn get_iterator_values(iterable: &Value) -> Result<Vec<Value>, CompileError> {
    match iterable {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(t) => Ok(t.clone()),
        Value::Str(s) => Ok(s.chars().map(|c| Value::Str(c.to_string())).collect()),
        Value::Generator(gen) => Ok(gen.collect_remaining()),
        Value::Object { class, fields } => {
            if class == "Range" {
                let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let end = fields.get("end").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let inclusive = fields.get("inclusive").map(|v| v.truthy()).unwrap_or(false);
                let mut values = Vec::new();
                if inclusive {
                    for i in start..=end {
                        values.push(Value::Int(i));
                    }
                } else {
                    for i in start..end {
                        values.push(Value::Int(i));
                    }
                }
                return Ok(values);
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("only arrays, tuples, strings, generators, and Range objects are iterable");
            Err(CompileError::semantic_with_context(
                format!("object of class '{}' is not iterable", class),
                ctx,
            ))
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("only arrays, tuples, strings, generators, and Range objects are iterable");
            Err(CompileError::semantic_with_context(
                format!("value of type '{}' is not iterable", iterable.type_name()),
                ctx,
            ))
        }
    }
}

/// Execute a block closure (BDD DSL colon-block)
/// Executes each statement in sequence and returns the last expression's value (or Nil)
pub(super) fn exec_block_closure(
    nodes: &[Node],
    captured_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::bdd::exec_block_value;

    // Diagram tracing for block closure execution
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call("<block>");
    }

    let mut local_env = captured_env.clone();
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                // Handle functional update (e.g., list->append(3))
                if let Expr::FunctionalUpdate { target, method, args } = expr {
                    if let Some((name, new_value)) = super::super::interpreter_helpers::handle_functional_update(
                        target,
                        method,
                        args,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )? {
                        local_env.insert(name, new_value);
                        last_value = Value::Nil;
                        continue;
                    }
                }
                // Handle self-updating method calls (e.g., arr.append(3))
                let (result, update) =
                    handle_method_call_with_self_update(expr, &mut local_env, functions, classes, enums, impl_methods)?;
                if let Some((name, new_self)) = update {
                    local_env.insert(name, new_self);
                }
                last_value = result;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, &mut local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(
                    &assign_stmt.value,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    // Check if this is a module-level global variable
                    let is_global = MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
                    if is_global && !local_env.contains_key(name) {
                        // Update module-level global
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(name.clone(), val);
                        });
                    } else {
                        // Update or create local variable
                        local_env.insert(name.clone(), val);
                    }
                } else if let simple_parser::ast::Expr::FieldAccess { receiver, field } = &assign_stmt.target {
                    // Handle field assignment: obj.field = value
                    if let simple_parser::ast::Expr::Identifier(obj_name) = receiver.as_ref() {
                        if let Some(obj_val) = local_env.get(obj_name).cloned() {
                            match obj_val {
                                Value::Object { class, mut fields } => {
                                    fields.insert(field.clone(), val);
                                    local_env.insert(obj_name.clone(), Value::Object { class, fields });
                                }
                                _ => {}
                            }
                        }
                    }
                }
                last_value = Value::Nil;
            }
            Node::Context(ctx_stmt) => {
                let context_obj = evaluate_expr(
                    &ctx_stmt.context,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;

                match &context_obj {
                    Value::Str(name) | Value::Symbol(name) => {
                        let name_str = if matches!(context_obj, Value::Symbol(_)) {
                            format!("with {}", name)
                        } else {
                            name.clone()
                        };

                        let ctx_def_blocks = if matches!(context_obj, Value::Symbol(_)) {
                            BDD_CONTEXT_DEFS.with(|cell| cell.borrow().get(name).cloned())
                        } else {
                            None
                        };

                        let indent = BDD_INDENT.with(|cell| *cell.borrow());
                        let indent_str = "  ".repeat(indent);

                        println!("{}{}", indent_str, name_str);

                        BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

                        BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
                        BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));

                        if let Some(ctx_blocks) = ctx_def_blocks {
                            for ctx_block in ctx_blocks {
                                exec_block_value(ctx_block, &mut local_env, functions, classes, enums, impl_methods)?;
                            }
                        }

                        last_value = exec_block_closure(
                            &ctx_stmt.body.statements,
                            &local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;

                        BDD_BEFORE_EACH.with(|cell| {
                            cell.borrow_mut().pop();
                        });
                        BDD_AFTER_EACH.with(|cell| {
                            cell.borrow_mut().pop();
                        });

                        BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);
                    }
                    _ => {
                        last_value = exec_block_closure(
                            &ctx_stmt.body.statements,
                            &local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    }
                }
            }
            Node::If(if_stmt) => {
                if let Some(pattern) = &if_stmt.let_pattern {
                    let value = evaluate_expr(
                        &if_stmt.condition,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums)? {
                        for (name, val) in bindings {
                            local_env.insert(name, val);
                        }
                        last_value = exec_block_closure_mut(
                            &if_stmt.then_block.statements,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(
                            &else_block.statements,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else {
                        last_value = Value::Nil;
                    }
                } else {
                    if evaluate_expr(
                        &if_stmt.condition,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?
                    .truthy()
                    {
                        last_value = exec_block_closure_mut(
                            &if_stmt.then_block.statements,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(
                            &else_block.statements,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else {
                        last_value = Value::Nil;
                    }
                }
            }
            Node::For(for_stmt) => {
                let iterable = evaluate_expr(
                    &for_stmt.iterable,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                let iter_values = get_iterator_values(&iterable)?;
                for val in iter_values {
                    if let simple_parser::ast::Pattern::Identifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                    // Use mutable env version so assignments inside the loop persist
                    last_value = exec_block_closure_mut(
                        &for_stmt.body.statements,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                }
            }
            Node::Function(f) => {
                // Handle function definitions inside block closures (like in `it` blocks)
                // The function is added to the local environment with the current scope captured
                local_env.insert(
                    f.name.clone(),
                    Value::Function {
                        name: f.name.clone(),
                        def: Box::new(f.clone()),
                        captured_env: local_env.clone(), // Capture current scope
                    },
                );
                last_value = Value::Nil;
            }
            Node::Class(class_def) => {
                // Handle class definitions inside block closures (like in `it` blocks)
                // The class is added to the classes map for the duration of this block
                classes.insert(class_def.name.clone(), class_def.clone());
                // Also add to local env as Constructor so it can be called like MyClass()
                local_env.insert(
                    class_def.name.clone(),
                    Value::Constructor {
                        class_name: class_def.name.clone(),
                    },
                );
                last_value = Value::Nil;
            }
            Node::Extern(ext) => {
                // Handle extern function declarations inside block closures (like in `it` blocks)
                // Register the extern function so it can be called within this block
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
                last_value = Value::Nil;
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}

/// Execute statements in an already-existing mutable environment.
/// Used for if-let blocks and for loop bodies where assignments should propagate to the outer scope.
fn exec_block_closure_mut(
    nodes: &[Node],
    local_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                // Handle self-updating method calls (e.g., arr.append(3))
                let (result, update) =
                    handle_method_call_with_self_update(expr, local_env, functions, classes, enums, impl_methods)?;
                if let Some((name, new_self)) = update {
                    local_env.insert(name, new_self);
                }
                last_value = result;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    // Check if this is a module-level global variable
                    let is_global = MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
                    if is_global && !local_env.contains_key(name) {
                        // Update module-level global
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(name.clone(), val);
                        });
                    } else {
                        // Update or create local variable
                        local_env.insert(name.clone(), val);
                    }
                } else if let simple_parser::ast::Expr::FieldAccess { receiver, field } = &assign_stmt.target {
                    // Handle field assignment: obj.field = value
                    if let simple_parser::ast::Expr::Identifier(obj_name) = receiver.as_ref() {
                        if let Some(obj_val) = local_env.get(obj_name).cloned() {
                            match obj_val {
                                Value::Object { class, mut fields } => {
                                    fields.insert(field.clone(), val);
                                    local_env.insert(obj_name.clone(), Value::Object { class, fields });
                                }
                                _ => {}
                            }
                        }
                    }
                }
                last_value = Value::Nil;
            }
            Node::If(if_stmt) => {
                if let Some(pattern) = &if_stmt.let_pattern {
                    let value = evaluate_expr(&if_stmt.condition, local_env, functions, classes, enums, impl_methods)?;
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums)? {
                        for (name, val) in bindings {
                            local_env.insert(name, val);
                        }
                        last_value = exec_block_closure_mut(
                            &if_stmt.then_block.statements,
                            local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(
                            &else_block.statements,
                            local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else {
                        last_value = Value::Nil;
                    }
                } else {
                    if evaluate_expr(&if_stmt.condition, local_env, functions, classes, enums, impl_methods)?.truthy() {
                        last_value = exec_block_closure_mut(
                            &if_stmt.then_block.statements,
                            local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(
                            &else_block.statements,
                            local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                    } else {
                        last_value = Value::Nil;
                    }
                }
            }
            Node::For(for_stmt) => {
                let iterable = evaluate_expr(&for_stmt.iterable, local_env, functions, classes, enums, impl_methods)?;
                let iter_values = get_iterator_values(&iterable)?;
                for val in iter_values {
                    if let simple_parser::ast::Pattern::Identifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                    last_value = exec_block_closure_mut(
                        &for_stmt.body.statements,
                        local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                }
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}
