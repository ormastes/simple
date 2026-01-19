// Node execution logic - statement and expression evaluation

use std::collections::HashMap;
use simple_parser::ast::{AssignOp, BinOp, ClassDef, Expr, FunctionDef, Node, Type};
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use super::core_types::{Control, Enums, ImplMethods, get_identifier_name, get_pattern_name, is_immutable_by_pattern};
use super::async_support::await_value;
use super::expr::evaluate_expr;
use super::interpreter_helpers::{bind_pattern_value, handle_method_call_with_self_update, handle_functional_update};
use super::interpreter_control::{exec_if, exec_while, exec_loop, exec_for, exec_match, exec_context, exec_with};
use super::interpreter_state::{mark_as_moved, CONST_NAMES, IMMUTABLE_VARS, MODULE_GLOBALS};
use crate::interpreter_unit::{is_unit_type, validate_unit_type, validate_unit_constraints};

pub(crate) fn exec_node(
    node: &Node,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    match node {
        Node::Let(let_stmt) => {
            if let Some(value_expr) = &let_stmt.value {
                // Handle method calls on objects - need to persist mutations to self
                let (value, update) =
                    handle_method_call_with_self_update(value_expr, env, functions, classes, enums, impl_methods)?;
                if let Some((obj_name, new_self)) = update {
                    env.insert(obj_name, new_self);
                }

                // Move semantics for unique pointers:
                // If binding a unique pointer from a simple identifier, mark source as moved
                if matches!(value, Value::Unique(_)) {
                    if let Some(source_name) = get_identifier_name(value_expr) {
                        mark_as_moved(source_name);
                    }
                }

                // Handle suspension operator (~=): await futures and promises
                let value = if let_stmt.is_suspend {
                    await_value(value)?
                } else {
                    value
                };

                // Validate unit type annotation if present
                // Type can come from either let_stmt.ty OR from a typed pattern (x: Type)
                let type_annotation = if let_stmt.ty.is_some() {
                    let_stmt.ty.clone()
                } else if let simple_parser::ast::Pattern::Typed { ty, .. } = &let_stmt.pattern {
                    Some(ty.clone())
                } else {
                    None
                };

                // Helper to extract variable name for error messages
                let get_var_name = |pattern: &simple_parser::ast::Pattern| -> String {
                    match pattern {
                        simple_parser::ast::Pattern::Identifier(name) => name.clone(),
                        simple_parser::ast::Pattern::MutIdentifier(name) => name.clone(),
                        simple_parser::ast::Pattern::Typed { pattern, .. } => match pattern.as_ref() {
                            simple_parser::ast::Pattern::Identifier(name) => name.clone(),
                            simple_parser::ast::Pattern::MutIdentifier(name) => name.clone(),
                            _ => "<pattern>".to_string(),
                        },
                        _ => "<pattern>".to_string(),
                    }
                };

                // Validate and constrain value based on type annotation
                let value = match &type_annotation {
                    Some(Type::Simple(type_name)) if is_unit_type(type_name) => {
                        if let Err(e) = validate_unit_type(&value, type_name) {
                            let var_name = get_var_name(&let_stmt.pattern);
                            return Err(crate::error::factory::let_binding_failed(&var_name, &e));
                        }
                        value
                    }
                    Some(Type::UnitWithRepr { name, constraints, .. }) => {
                        // Validate and apply unit type constraints (range, overflow behavior)
                        match validate_unit_constraints(value, name, constraints) {
                            Ok(constrained_value) => constrained_value,
                            Err(e) => {
                                let var_name = get_var_name(&let_stmt.pattern);
                                return Err(crate::error::factory::let_binding_failed(&var_name, &e));
                            }
                        }
                    }
                    _ => value,
                };

                // Coerce to TraitObject if type annotation is `dyn Trait`
                let value = if let Some(Type::DynTrait(trait_name)) = &let_stmt.ty {
                    Value::TraitObject {
                        trait_name: trait_name.clone(),
                        inner: Box::new(value),
                    }
                } else {
                    value
                };
                let is_mutable = let_stmt.mutability.is_mutable();
                bind_pattern_value(&let_stmt.pattern, value, is_mutable, env);
            }
            Ok(Control::Next)
        }
        Node::Const(const_stmt) => {
            // E1024 - Const Eval Failed
            let value = evaluate_expr(&const_stmt.value, env, functions, classes, enums, impl_methods)
                .map_err(|e| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::CONST_EVAL_FAILED)
                        .with_help("constant expressions must be evaluable at compile time")
                        .with_note(format!("error occurred while evaluating constant `{}`", const_stmt.name));
                    CompileError::semantic_with_context(
                        format!("failed to evaluate constant `{}`: {}", const_stmt.name, e),
                        ctx,
                    )
                })?;
            env.insert(const_stmt.name.clone(), value);
            CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
            Ok(Control::Next)
        }
        Node::Static(static_stmt) => {
            let value = evaluate_expr(&static_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(static_stmt.name.clone(), value);
            if !static_stmt.mutability.is_mutable() {
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
            }
            Ok(Control::Next)
        }
        Node::Assignment(assign) if assign.op == AssignOp::Assign => {
            exec_assignment(assign, env, functions, classes, enums, impl_methods)
        }
        // Handle augmented assignments (+=, -=, *=, /=) and suspension variants (~+=, ~-=, etc.)
        Node::Assignment(assign) => exec_augmented_assignment(assign, env, functions, classes, enums, impl_methods),
        Node::If(if_stmt) => exec_if(if_stmt, env, functions, classes, enums, impl_methods),
        Node::While(while_stmt) => exec_while(while_stmt, env, functions, classes, enums, impl_methods),
        Node::Loop(loop_stmt) => exec_loop(loop_stmt, env, functions, classes, enums, impl_methods),
        Node::For(for_stmt) => exec_for(for_stmt, env, functions, classes, enums, impl_methods),
        Node::Return(ret) => {
            let value = if let Some(expr) = &ret.value {
                // Handle method calls on objects - need to persist mutations to self
                let (val, update) =
                    handle_method_call_with_self_update(expr, env, functions, classes, enums, impl_methods)?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }
                val
            } else {
                Value::Nil
            };
            Ok(Control::Return(value))
        }
        Node::Break(b) => {
            let value = if let Some(expr) = &b.value {
                Some(evaluate_expr(expr, env, functions, classes, enums, impl_methods)?)
            } else {
                None
            };
            Ok(Control::Break(value))
        }
        Node::Continue(_) => Ok(Control::Continue),
        Node::Match(match_stmt) => exec_match(match_stmt, env, functions, classes, enums, impl_methods),
        Node::Context(ctx_stmt) => exec_context(ctx_stmt, env, functions, classes, enums, impl_methods),
        Node::With(with_stmt) => exec_with(with_stmt, env, functions, classes, enums, impl_methods),
        Node::Expression(expr) => {
            if let Expr::FunctionalUpdate { target, method, args } = expr {
                if let Some((name, new_value)) =
                    handle_functional_update(target, method, args, env, functions, classes, enums, impl_methods)?
                {
                    env.insert(name, new_value);
                    return Ok(Control::Next);
                }
            }
            // Handle method calls on objects - need to persist mutations to self
            let (_, update) = handle_method_call_with_self_update(expr, env, functions, classes, enums, impl_methods)?;
            if let Some((name, new_self)) = update {
                env.insert(name, new_self);
            }
            Ok(Control::Next)
        }
        Node::Function(f) => {
            // Nested function definition - treat as a closure that captures the current scope
            // Store as a Function with the captured env embedded for closure semantics
            env.insert(
                f.name.clone(),
                Value::Function {
                    name: f.name.clone(),
                    def: Box::new(f.clone()),
                    captured_env: env.clone(), // Capture current scope
                },
            );
            Ok(Control::Next)
        }
        _ => Ok(Control::Next),
    }
}

// Helper function for regular assignment
fn exec_assignment(
    assign: &simple_parser::ast::AssignmentStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    if let Expr::Identifier(name) = &assign.target {
        // Check if this is a first-time assignment (implicit declaration)
        let is_first_assignment = !env.contains_key(name);

        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            return Err(crate::error::factory::cannot_assign_to_const(name));
        }

        // Check immutability for reassignments (not first assignment)
        if !is_first_assignment {
            let is_immutable = IMMUTABLE_VARS.with(|cell| cell.borrow().contains(name));
            if is_immutable && !name.ends_with('_') {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help(format!("consider using '{name}_' for a mutable variable, or use '{name}->method()' for functional updates"));
                return Err(CompileError::semantic_with_context(
                    format!("invalid assignment: cannot reassign to immutable variable '{}'", name),
                    ctx,
                ));
            }
        }

        // Handle method calls on objects - need to persist mutations to self
        let (value, update) =
            handle_method_call_with_self_update(&assign.value, env, functions, classes, enums, impl_methods)?;
        // If the mutating method returned an updated object with the same name as target,
        // the update already set the variable, so skip the normal assignment
        let skip_assignment = if let Some((ref obj_name, ref new_self)) = update {
            env.insert(obj_name.clone(), new_self.clone());
            obj_name == name
        } else {
            false
        };
        if !skip_assignment {
            // Check if this is a module-level global variable (for function access)
            let is_global = MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
            if is_global && !env.contains_key(name) {
                // Update module-level global
                MODULE_GLOBALS.with(|cell| {
                    cell.borrow_mut().insert(name.clone(), value);
                });
            } else {
                env.insert(name.clone(), value);

                // If this is a first-time assignment (implicit declaration),
                // track its mutability based on naming pattern
                if is_first_assignment {
                    let immutable_by_pattern = is_immutable_by_pattern(name);
                    let is_all_caps = name.chars().all(|c| c.is_uppercase() || c.is_numeric() || c == '_')
                        && name.chars().any(|c| c.is_alphabetic());

                    if immutable_by_pattern {
                        if is_all_caps {
                            // ALL_CAPS = constant
                            CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                        } else {
                            // Lowercase = immutable (supports functional updates)
                            IMMUTABLE_VARS.with(|cell| cell.borrow_mut().insert(name.clone()));
                        }
                    }
                    // else: ends with _ = mutable, no tracking needed
                }

                // Also sync to MODULE_GLOBALS if it exists there (for module-level assignments)
                MODULE_GLOBALS.with(|cell| {
                    let mut globals = cell.borrow_mut();
                    if globals.contains_key(name) {
                        globals.insert(name.clone(), env.get(name).unwrap().clone());
                    }
                });
            }
        }
        Ok(Control::Next)
    } else if let Expr::FieldAccess { receiver, field } = &assign.target {
        // Handle field assignment: obj.field = value
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        // Get the object name (must be an identifier for now)
        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            if let Some(obj_val) = env.get(obj_name).cloned() {
                match obj_val {
                    Value::Object { class, mut fields } => {
                        fields.insert(field.clone(), value);
                        env.insert(obj_name.clone(), Value::Object { class, fields });
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("field assignment requires an object with mutable access");
                        return Err(CompileError::semantic_with_context(
                            "invalid assignment: cannot assign field on non-object value",
                            ctx,
                        ))
                    }
                }
                Ok(Control::Next)
            } else {
                // Collect all known names for typo suggestion
                let known_names: Vec<&str> = env
                    .keys()
                    .map(|s| s.as_str())
                    .chain(functions.keys().map(|s| s.as_str()))
                    .chain(classes.keys().map(|s| s.as_str()))
                    .collect();
                // E1001 - Undefined Variable
                let suggestion = crate::error::typo::suggest_name(obj_name, known_names.clone());
                let mut ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_VARIABLE)
                    .with_help("check that the variable is defined and in scope");

                if let Some(best_match) = suggestion {
                    ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                }

                Err(CompileError::semantic_with_context(
                    format!("variable `{}` not found", obj_name),
                    ctx,
                ))
            }
        } else {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help("field assignment requires an identifier as the object");
            Err(CompileError::semantic_with_context(
                "invalid assignment: field assignment requires identifier as object",
                ctx,
            ))
        }
    } else if let Expr::Index { receiver, index } = &assign.target {
        // Handle index assignment: arr[i] = value or dict["key"] = value
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        let index_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;

        // Get the container name (must be an identifier for now)
        if let Expr::Identifier(container_name) = receiver.as_ref() {
            if let Some(container) = env.get(container_name).cloned() {
                let new_container = match container {
                    Value::Array(mut arr) => {
                        let idx = index_val.as_int()? as usize;
                        if idx < arr.len() {
                            arr[idx] = value;
                        } else {
                            // Extend array if index is at the end
                            while arr.len() < idx {
                                arr.push(Value::Nil);
                            }
                            arr.push(value);
                        }
                        Value::Array(arr)
                    }
                    Value::Dict(mut dict) => {
                        let key = index_val.to_key_string();
                        dict.insert(key, value);
                        Value::Dict(dict)
                    }
                    Value::Tuple(mut tup) => {
                        let idx = index_val.as_int()? as usize;
                        if idx < tup.len() {
                            tup[idx] = value;
                            Value::Tuple(tup)
                        } else {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                .with_help(format!("tuple has {} element(s)", tup.len()))
                                .with_note(format!("index {} is out of bounds", idx));
                            return Err(CompileError::semantic_with_context(
                                format!("index out of bounds: tuple index {} out of bounds (len={})", idx, tup.len()),
                                ctx,
                            ));
                        }
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("index assignment requires an array, dict, or tuple");
                        return Err(CompileError::semantic_with_context(
                            format!("invalid assignment: cannot index assign value of type {}", container.type_name()),
                            ctx,
                        ))
                    }
                };
                env.insert(container_name.clone(), new_container);
                Ok(Control::Next)
            } else {
                // E1001 - Undefined Variable
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_VARIABLE)
                    .with_help("check that the variable is defined and in scope");
                Err(CompileError::semantic_with_context(
                    format!("variable `{}` not found", container_name),
                    ctx,
                ))
            }
        } else {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help("index assignment requires an identifier as the container");
            Err(CompileError::semantic_with_context(
                "invalid assignment: index assignment requires identifier as container",
                ctx,
            ))
        }
    } else if let Expr::Tuple(targets) = &assign.target {
        // Handle tuple unpacking: (a, b) = (x, y)
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        let values: Vec<Value> = match value {
            Value::Tuple(v) => v,
            Value::Array(v) => v,
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("tuple unpacking requires a tuple or array on the right side");
                return Err(CompileError::semantic_with_context(
                    format!("type mismatch: tuple unpacking requires tuple or array, got {}", value.type_name()),
                    ctx,
                ))
            }
        };
        if targets.len() != values.len() {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("ensure the right side has the same number of elements as the left side");
            return Err(CompileError::semantic_with_context(
                format!("argument count mismatch: tuple unpacking expected {}, got {}", targets.len(), values.len()),
                ctx,
            ));
        }
        for (target_expr, val) in targets.iter().zip(values.into_iter()) {
            if let Expr::Identifier(name) = target_expr {
                env.insert(name.clone(), val);
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help("tuple unpacking targets must be identifiers");
                return Err(CompileError::semantic_with_context(
                    "invalid assignment: tuple unpacking target must be identifier",
                    ctx,
                ));
            }
        }
        Ok(Control::Next)
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_LHS_ASSIGNMENT)
            .with_help("assignment target must be a variable, field, or array index");
        Err(CompileError::semantic_with_context(
            "invalid assignment: unsupported assignment target",
            ctx,
        ))
    }
}

// Helper function for augmented assignment
fn exec_augmented_assignment(
    assign: &simple_parser::ast::AssignmentStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Check if this is a suspension assignment that needs await
    let is_suspend = matches!(
        assign.op,
        AssignOp::SuspendAssign
            | AssignOp::SuspendAddAssign
            | AssignOp::SuspendSubAssign
            | AssignOp::SuspendMulAssign
            | AssignOp::SuspendDivAssign
    );

    // Get the binary operation corresponding to the augmented assign op
    let bin_op = match assign.op {
        AssignOp::AddAssign | AssignOp::SuspendAddAssign => Some(BinOp::Add),
        AssignOp::SubAssign | AssignOp::SuspendSubAssign => Some(BinOp::Sub),
        AssignOp::MulAssign | AssignOp::SuspendMulAssign => Some(BinOp::Mul),
        AssignOp::DivAssign | AssignOp::SuspendDivAssign => Some(BinOp::Div),
        AssignOp::SuspendAssign => None, // ~= is simple await assignment
        AssignOp::Assign => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("plain assignment (=) should be handled by the standard assignment function");
            return Err(CompileError::semantic_with_context(
                "invalid operation: plain assignment should be handled elsewhere",
                ctx,
            ))
        }
    };

    // Handle identifier targets: x += 1 or x ~+= promise
    if let Expr::Identifier(name) = &assign.target {
        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            return Err(crate::error::factory::cannot_assign_to_const(name));
        }

        // Evaluate the RHS
        let mut rhs_value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;

        // If suspension, await the value
        if is_suspend {
            rhs_value = await_value(rhs_value)?;
        }

        // If compound assignment, combine with current value
        let new_value = if let Some(op) = bin_op {
            // Create a binary expression and evaluate it
            let current = env
                .get(name)
                .cloned()
                .ok_or_else(|| {
                    // E1001 - Undefined Variable
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("check that the variable is defined and in scope");
                    CompileError::semantic_with_context(
                        format!("variable `{}` not found", name),
                        ctx,
                    )
                })?;
            // Insert rhs as temp var, create binary expr, evaluate
            let temp_name = "__rhs_temp__".to_string();
            env.insert(temp_name.clone(), rhs_value);
            let binary_expr = Expr::Binary {
                op,
                left: Box::new(assign.target.clone()),
                right: Box::new(Expr::Identifier(temp_name.clone())),
            };
            let result = evaluate_expr(&binary_expr, env, functions, classes, enums, impl_methods)?;
            env.remove(&temp_name);
            result
        } else {
            // Simple ~= assignment
            rhs_value
        };

        env.insert(name.clone(), new_value);
        Ok(Control::Next)
    }
    // Handle field access targets: obj.field += 1
    else if let Expr::FieldAccess { receiver, field } = &assign.target {
        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            if let Some(obj_val) = env.get(obj_name).cloned() {
                match obj_val {
                    Value::Object { class, mut fields } => {
                        // Evaluate the RHS
                        let mut rhs_value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;

                        // If suspension, await the value
                        if is_suspend {
                            rhs_value = await_value(rhs_value)?;
                        }

                        // If compound assignment, combine with current value
                        let new_value = if let Some(op) = bin_op {
                            // Create a binary expression and evaluate it
                            let current = fields
                                .get(field)
                                .cloned()
                                .ok_or_else(|| crate::error::factory::undefined_field(field))?;
                            // Insert temps and evaluate
                            let temp_lhs = "__lhs_temp__".to_string();
                            let temp_rhs = "__rhs_temp__".to_string();
                            env.insert(temp_lhs.clone(), current);
                            env.insert(temp_rhs.clone(), rhs_value);
                            let binary_expr = Expr::Binary {
                                op,
                                left: Box::new(Expr::Identifier(temp_lhs.clone())),
                                right: Box::new(Expr::Identifier(temp_rhs.clone())),
                            };
                            let result = evaluate_expr(&binary_expr, env, functions, classes, enums, impl_methods)?;
                            env.remove(&temp_lhs);
                            env.remove(&temp_rhs);
                            result
                        } else {
                            rhs_value
                        };

                        fields.insert(field.clone(), new_value);
                        env.insert(obj_name.clone(), Value::Object { class, fields });
                        Ok(Control::Next)
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("augmented assignment on fields requires an object value");
                        Err(CompileError::semantic_with_context(
                            "invalid assignment: cannot use augmented assignment on non-object value",
                            ctx,
                        ))
                    },
                }
            } else {
                // E1001 - Undefined Variable
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_VARIABLE)
                    .with_help("check that the variable is defined and in scope");
                Err(CompileError::semantic_with_context(
                    format!("variable `{}` not found", obj_name),
                    ctx,
                ))
            }
        } else {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help("augmented field assignment requires an identifier as the object");
            Err(CompileError::semantic_with_context(
                "invalid assignment: augmented field assignment requires identifier as object",
                ctx,
            ))
        }
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_ASSIGNMENT)
            .with_help("augmented assignment target must be a variable, field, or array index");
        Err(CompileError::semantic_with_context(
            "invalid assignment: unsupported augmented assignment target",
            ctx,
        ))
    }
}
