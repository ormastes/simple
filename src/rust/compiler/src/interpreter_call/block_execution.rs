// Block closure execution helpers for interpreter_call module

use super::super::interpreter_helpers::{bind_pattern_value, handle_method_call_with_self_update};
use super::bdd::{BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_INDENT};
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    evaluate_expr, exec_with, get_type_name, pattern_matches, BLOCK_SCOPED_ENUMS, CONST_NAMES, EXTERN_FUNCTIONS,
    IMMUTABLE_VARS, MACRO_DEFINITION_ORDER, MIXINS, MODULE_GLOBALS, TRAIT_IMPLS, TRAITS, USER_MACROS,
};
use crate::value::*;
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Node};
use simple_runtime::value::diagram_ffi;
use std::collections::HashMap;
use std::sync::Arc;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

fn get_iterator_values(iterable: &Value) -> Result<Vec<Value>, CompileError> {
    match iterable {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(t) => Ok(t.clone()),
        Value::Str(s) => Ok(s.chars().map(|c| Value::Str(c.to_string())).collect()),
        Value::Generator(gen) => Ok(gen.collect_remaining()),
        Value::Dict(map) => {
            // Iterate over dict returns (key, value) tuples
            let entries: Vec<Value> = map
                .iter()
                .map(|(k, v)| Value::Tuple(vec![Value::Str(k.clone()), v.clone()]))
                .collect();
            Ok(entries)
        }
        Value::Object { class, fields } => {
            if class == "Range" || class == BUILTIN_RANGE {
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
                .with_help("only arrays, tuples, strings, dicts, generators, and Range objects are iterable");
            Err(CompileError::semantic_with_context(
                format!("object of class '{}' is not iterable", class),
                ctx,
            ))
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("only arrays, tuples, strings, dicts, generators, and Range objects are iterable");
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

    // Save current CONST_NAMES and IMMUTABLE_VARS, clear for block closure scope
    // This prevents const/immutable names from caller leaking into the block
    let saved_const_names = CONST_NAMES.with(|cell| cell.borrow().clone());
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    let saved_immutable_vars = IMMUTABLE_VARS.with(|cell| cell.borrow().clone());
    IMMUTABLE_VARS.with(|cell| cell.borrow_mut().clear());

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
                    // Handle method calls with self-update (e.g., m.call("method", []))
                    let (val, update) = handle_method_call_with_self_update(
                        value_expr,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    if let Some((obj_name, new_self)) = update {
                        local_env.insert(obj_name, new_self);
                    }
                    // Use bind_pattern_value to handle all pattern types including tuples
                    let is_mutable = let_stmt.mutability.is_mutable();
                    bind_pattern_value(&let_stmt.pattern, val, is_mutable, &mut local_env);
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
                                Value::Object { class, fields } => {
                                    let mut fields = fields;
                                    Arc::make_mut(&mut fields).insert(field.clone(), val);
                                    local_env.insert(obj_name.clone(), Value::Object { class, fields });
                                }
                                _ => {}
                            }
                        }
                    }
                } else if let simple_parser::ast::Expr::Index { receiver, index } = &assign_stmt.target {
                    // Handle index assignment: arr[i] = value or dict["key"] = value
                    let index_val = evaluate_expr(index, &mut local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Expr::Identifier(container_name) = receiver.as_ref() {
                        if let Some(container) = local_env.get(container_name).cloned() {
                            let new_container = match container {
                                Value::Array(mut arr) => {
                                    let idx = index_val.as_int()? as usize;
                                    if idx < arr.len() {
                                        arr[idx] = val;
                                    } else {
                                        while arr.len() < idx {
                                            arr.push(Value::Nil);
                                        }
                                        arr.push(val);
                                    }
                                    Value::Array(arr)
                                }
                                Value::Dict(mut dict) => {
                                    let key = index_val.to_key_string();
                                    dict.insert(key, val);
                                    Value::Dict(dict)
                                }
                                Value::Tuple(mut tup) => {
                                    let idx = index_val.as_int()? as usize;
                                    if idx < tup.len() {
                                        tup[idx] = val;
                                    }
                                    Value::Tuple(tup)
                                }
                                _ => container,
                            };
                            local_env.insert(container_name.clone(), new_container);
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
                    } else if let simple_parser::ast::Pattern::MoveIdentifier(ref name) = for_stmt.pattern {
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
            Node::With(with_stmt) => {
                // Handle context manager (with statement) inside block closures
                // Delegates to the main interpreter's exec_with function
                use crate::interpreter::Control;
                match exec_with(with_stmt, &mut local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(val) => {
                        // Restore CONST_NAMES and IMMUTABLE_VARS before returning
                        CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
                        IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
                        return Ok(val);
                    }
                    _ => last_value = Value::Nil,
                }
            }
            Node::Macro(m) => {
                // Handle macro definitions inside block closures (e.g., in `it` blocks)
                // Register the macro in USER_MACROS so it can be invoked within this block
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
                // Track macro definition order for validation
                MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().push(m.name.clone()));
                last_value = Value::Nil;
            }
            Node::Enum(e) => {
                // Handle enum definitions inside block closures (e.g., in `it` blocks)
                // Register the enum type in the local environment so EnumName.VariantName works
                local_env.insert(
                    e.name.clone(),
                    Value::EnumType {
                        enum_name: e.name.clone(),
                    },
                );
                // Also register in BLOCK_SCOPED_ENUMS for pattern matching support
                BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), e.clone()));
                last_value = Value::Nil;
            }
            Node::Struct(s) => {
                // Handle struct definitions inside block closures (e.g., in `it` blocks)
                local_env.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
                classes.insert(
                    s.name.clone(),
                    ClassDef {
                        span: s.span,
                        name: s.name.clone(),
                        generic_params: Vec::new(),
                        where_clause: vec![],
                        fields: s.fields.clone(),
                        methods: s.methods.clone(),
                        parent: None,
                        visibility: s.visibility,
                        effects: Vec::new(),
                        attributes: Vec::new(),
                        doc_comment: None,
                        invariant: None,
                        macro_invocations: vec![],
                        mixins: vec![],
                        is_generic_template: false,
                        specialization_of: None,
                        type_bindings: std::collections::HashMap::new(),
                    },
                );
                last_value = Value::Nil;
            }
            Node::Class(c) => {
                // Handle class definitions inside block closures (e.g., in `it` blocks)
                classes.insert(c.name.clone(), c.clone());
                local_env.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
                last_value = Value::Nil;
            }
            Node::Trait(trait_def) => {
                // Handle trait definitions inside block closures (e.g., in `it` blocks)
                // Register the trait definition in TRAITS thread-local
                TRAITS.with(|cell| {
                    cell.borrow_mut().insert(trait_def.name.clone(), trait_def.clone());
                });
                last_value = Value::Nil;
            }
            Node::Mixin(mixin_def) => {
                MIXINS.with(|cell| {
                    cell.borrow_mut().insert(mixin_def.name.clone(), mixin_def.clone());
                });
                last_value = Value::Nil;
            }
            Node::Impl(impl_block) => {
                // Handle impl blocks inside block closures (e.g., in `it` blocks)
                // Register the impl methods so they can be found during method dispatch
                let type_name = get_type_name(&impl_block.target_type);

                // If this is a trait implementation, merge with default trait methods
                if let Some(ref trait_name) = impl_block.trait_name {
                    // Look up the trait definition
                    let trait_def_opt = TRAITS.with(|cell| cell.borrow().get(trait_name).cloned());

                    if let Some(trait_def) = trait_def_opt {
                        // Build combined methods: impl methods + default trait methods
                        let mut combined_methods = impl_block.methods.clone();
                        let impl_method_names: std::collections::HashSet<_> =
                            impl_block.methods.iter().map(|m| m.name.clone()).collect();

                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                combined_methods.push(trait_method.clone());
                            }
                        }

                        // Register in TRAIT_IMPLS with combined methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                combined_methods.clone(),
                            );
                        });

                        // Merge impl methods into ClassDef (mirrors interpreter_eval.rs:358-359)
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            class_def.methods.extend(combined_methods);
                        }
                    } else {
                        // Trait not found - just register the impl methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                impl_block.methods.clone(),
                            );
                        });

                        // Merge impl methods into ClassDef
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            class_def.methods.extend(impl_block.methods.clone());
                        }
                    }
                } else {
                    // Non-trait impl block - merge methods into ClassDef
                    if let Some(class_def) = classes.get_mut(&type_name) {
                        class_def.methods.extend(impl_block.methods.clone());
                    }
                }

                last_value = Value::Nil;
            }
            Node::Const(const_stmt) => {
                // Evaluate const value
                let value = evaluate_expr(
                    &const_stmt.value,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                // Insert into local environment
                local_env.insert(const_stmt.name.clone(), value);
                // Register as const name
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
                last_value = Value::Nil;
            }
            Node::Static(static_stmt) => {
                // Evaluate static value
                let value = evaluate_expr(
                    &static_stmt.value,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                // Insert into local environment
                local_env.insert(static_stmt.name.clone(), value);
                // Register as const if immutable
                if !static_stmt.mutability.is_mutable() {
                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
                }
                last_value = Value::Nil;
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    // Restore CONST_NAMES and IMMUTABLE_VARS before returning
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
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
                    // Handle method calls with self-update (e.g., m.call("method", []))
                    let (val, update) = handle_method_call_with_self_update(
                        value_expr,
                        local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    if let Some((obj_name, new_self)) = update {
                        local_env.insert(obj_name, new_self);
                    }
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MoveIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                // Handle method calls with self-update for assignment RHS
                let (val, update) = handle_method_call_with_self_update(
                    &assign_stmt.value,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                if let Some((obj_name, new_self)) = update {
                    local_env.insert(obj_name, new_self);
                }
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
                                Value::Object { class, fields } => {
                                    let mut fields = fields;
                                    Arc::make_mut(&mut fields).insert(field.clone(), val);
                                    local_env.insert(obj_name.clone(), Value::Object { class, fields });
                                }
                                _ => {}
                            }
                        }
                    }
                } else if let simple_parser::ast::Expr::Index { receiver, index } = &assign_stmt.target {
                    // Handle index assignment: arr[i] = value or dict["key"] = value
                    let index_val = evaluate_expr(index, local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Expr::Identifier(container_name) = receiver.as_ref() {
                        if let Some(container) = local_env.get(container_name).cloned() {
                            let new_container = match container {
                                Value::Array(mut arr) => {
                                    let idx = index_val.as_int()? as usize;
                                    if idx < arr.len() {
                                        arr[idx] = val;
                                    } else {
                                        while arr.len() < idx {
                                            arr.push(Value::Nil);
                                        }
                                        arr.push(val);
                                    }
                                    Value::Array(arr)
                                }
                                Value::Dict(mut dict) => {
                                    let key = index_val.to_key_string();
                                    dict.insert(key, val);
                                    Value::Dict(dict)
                                }
                                Value::Tuple(mut tup) => {
                                    let idx = index_val.as_int()? as usize;
                                    if idx < tup.len() {
                                        tup[idx] = val;
                                    }
                                    Value::Tuple(tup)
                                }
                                _ => container,
                            };
                            local_env.insert(container_name.clone(), new_container);
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
                    } else if let simple_parser::ast::Pattern::MoveIdentifier(ref name) = for_stmt.pattern {
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
            Node::With(with_stmt) => {
                // Handle context manager (with statement) inside block closures
                // Delegates to the main interpreter's exec_with function
                use crate::interpreter::Control;
                match exec_with(with_stmt, local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(val) => return Ok(val),
                    _ => last_value = Value::Nil,
                }
            }
            Node::Macro(m) => {
                // Handle macro definitions inside block closures (e.g., in `it` blocks)
                // Register the macro in USER_MACROS so it can be invoked within this block
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
                // Track macro definition order for validation
                MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().push(m.name.clone()));
                last_value = Value::Nil;
            }
            Node::Enum(e) => {
                // Handle enum definitions inside block closures (e.g., in `it` blocks)
                // Register the enum type in the local environment so EnumName.VariantName works
                local_env.insert(
                    e.name.clone(),
                    Value::EnumType {
                        enum_name: e.name.clone(),
                    },
                );
                // Also register in BLOCK_SCOPED_ENUMS for pattern matching support
                BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), e.clone()));
                last_value = Value::Nil;
            }
            Node::Struct(s) => {
                local_env.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
                classes.insert(
                    s.name.clone(),
                    ClassDef {
                        span: s.span,
                        name: s.name.clone(),
                        generic_params: Vec::new(),
                        where_clause: vec![],
                        fields: s.fields.clone(),
                        methods: s.methods.clone(),
                        parent: None,
                        visibility: s.visibility,
                        effects: Vec::new(),
                        attributes: Vec::new(),
                        doc_comment: None,
                        invariant: None,
                        macro_invocations: vec![],
                        mixins: vec![],
                        is_generic_template: false,
                        specialization_of: None,
                        type_bindings: std::collections::HashMap::new(),
                    },
                );
                last_value = Value::Nil;
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                local_env.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
                last_value = Value::Nil;
            }
            Node::Trait(trait_def) => {
                // Handle trait definitions inside block closures (e.g., in `it` blocks)
                // Register the trait definition in TRAITS thread-local
                TRAITS.with(|cell| {
                    cell.borrow_mut().insert(trait_def.name.clone(), trait_def.clone());
                });
                last_value = Value::Nil;
            }
            Node::Mixin(mixin_def) => {
                MIXINS.with(|cell| {
                    cell.borrow_mut().insert(mixin_def.name.clone(), mixin_def.clone());
                });
                last_value = Value::Nil;
            }
            Node::Impl(impl_block) => {
                // Handle impl blocks inside block closures (e.g., in `it` blocks)
                // Register the impl methods so they can be found during method dispatch
                let type_name = get_type_name(&impl_block.target_type);

                // If this is a trait implementation, merge with default trait methods
                if let Some(ref trait_name) = impl_block.trait_name {
                    // Look up the trait definition
                    let trait_def_opt = TRAITS.with(|cell| cell.borrow().get(trait_name).cloned());

                    if let Some(trait_def) = trait_def_opt {
                        // Build combined methods: impl methods + default trait methods
                        let mut combined_methods = impl_block.methods.clone();
                        let impl_method_names: std::collections::HashSet<_> =
                            impl_block.methods.iter().map(|m| m.name.clone()).collect();

                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                combined_methods.push(trait_method.clone());
                            }
                        }

                        // Register in TRAIT_IMPLS with combined methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                combined_methods.clone(),
                            );
                        });

                        // Merge impl methods into ClassDef (mirrors interpreter_eval.rs:358-359)
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            class_def.methods.extend(combined_methods);
                        }
                    } else {
                        // Trait not found - just register the impl methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                impl_block.methods.clone(),
                            );
                        });

                        // Merge impl methods into ClassDef
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            class_def.methods.extend(impl_block.methods.clone());
                        }
                    }
                } else {
                    // Non-trait impl block - merge methods into ClassDef
                    if let Some(class_def) = classes.get_mut(&type_name) {
                        class_def.methods.extend(impl_block.methods.clone());
                    }
                }

                last_value = Value::Nil;
            }
            Node::Const(const_stmt) => {
                // Evaluate const value
                let value = evaluate_expr(
                    &const_stmt.value,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                // Insert into environment
                local_env.insert(const_stmt.name.clone(), value);
                // Register as const name
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
                last_value = Value::Nil;
            }
            Node::Static(static_stmt) => {
                // Evaluate static value
                let value = evaluate_expr(
                    &static_stmt.value,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                // Insert into environment
                local_env.insert(static_stmt.name.clone(), value);
                // Register as const if immutable
                if !static_stmt.mutability.is_mutable() {
                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
                }
                last_value = Value::Nil;
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}
