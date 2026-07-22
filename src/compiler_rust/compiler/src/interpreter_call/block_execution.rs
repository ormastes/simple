// Block closure execution helpers for interpreter_call module

use super::super::interpreter_control::{is_condition_present, optional_let_binding, LetBind};
use super::super::interpreter_helpers::{bind_pattern_value, handle_method_call_with_self_update};
use super::bdd::{BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_INDENT};
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    evaluate_expr, exec_assignment, exec_augmented_assignment, exec_with, get_type_name, pattern_matches,
    BLOCK_SCOPED_ENUMS, CONST_NAMES, CONTEXT_OBJECT, CONTEXT_VAR_NAME, EXTERN_FUNCTIONS, GLOBAL_ENUMS, IMMUTABLE_VARS,
    MACRO_DEFINITION_ORDER, MIXINS, MODULE_GLOBALS, TRAIT_IMPLS, TRAITS, USER_MACROS,
};
use crate::value::*;
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Node};
use simple_runtime::value::diagram_sffi;
use std::collections::HashMap;
use std::sync::Arc;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

/// Inject mixin fields and methods into a ClassDef.
/// Returns a new ClassDef with mixin fields prepended and mixin methods appended.
fn inject_mixins(class_def: &ClassDef) -> ClassDef {
    if class_def.mixins.is_empty() {
        return class_def.clone();
    }
    let mut updated = class_def.clone();
    let existing_method_names: std::collections::HashSet<_> =
        class_def.methods.iter().map(|m| m.name.clone()).collect();
    let mut mixin_fields = Vec::new();
    let mut mixin_methods = Vec::new();
    let mut seen_field_names: std::collections::HashSet<String> =
        class_def.fields.iter().map(|f| f.name.clone()).collect();
    let mut seen_method_names = existing_method_names;
    MIXINS.with(|cell| {
        let registry = cell.borrow();
        // Transitive resolution: BFS through mixin dependencies
        let mut seen_mixins = std::collections::HashSet::new();
        let mut queue: std::collections::VecDeque<String> = class_def.mixins.iter().map(|m| m.name.clone()).collect();
        while let Some(mixin_name) = queue.pop_front() {
            if !seen_mixins.insert(mixin_name.clone()) {
                continue; // Diamond dedup
            }
            if let Some(mixin_def) = registry.get(&mixin_name) {
                // Queue transitive dependencies
                for req in &mixin_def.required_mixins {
                    queue.push_back(req.clone());
                }
                // Collect fields (dedup by name)
                for field in &mixin_def.fields {
                    if seen_field_names.insert(field.name.clone()) {
                        mixin_fields.push(field.clone());
                    }
                }
                // Collect methods (skip if class or earlier mixin defines same name)
                for method in &mixin_def.methods {
                    if seen_method_names.insert(method.name.clone()) {
                        mixin_methods.push(method.clone());
                    }
                }
            }
        }
    });
    if !mixin_fields.is_empty() {
        updated.fields.splice(0..0, mixin_fields);
    }
    updated.methods.extend(mixin_methods);
    updated
}

fn get_iterator_values(iterable: &Value) -> Result<Vec<Value>, CompileError> {
    match iterable {
        Value::Array(arr) => Ok(arr.to_vec()),
        Value::FrozenArray(arr) => Ok(arr.as_ref().clone()),
        Value::FixedSizeArray { data, .. } => Ok(data.clone()),
        Value::Tuple(t) => Ok(t.clone()),
        Value::Str(s) => Ok(s.chars().map(|c| Value::text(c.to_string())).collect()),
        Value::Generator(gen) => Ok(gen.collect_remaining()),
        Value::FrozenDict(map) => {
            let entries: Vec<Value> = map
                .iter()
                .map(|(k, v)| Value::Tuple(vec![Value::text(k.clone()), v.clone()]))
                .collect();
            Ok(entries)
        }
        Value::Dict(map) => {
            // Iterate over dict returns (key, value) tuples
            let entries: Vec<Value> = map
                .iter()
                .map(|(k, v)| Value::Tuple(vec![Value::text(k.clone()), v.clone()]))
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

/// Execute a block closure (BDD DSL colon-block) against a fresh scope.
/// Executes each statement in sequence and returns the last expression's value (or Nil).
/// This is the clone-isolated wrapper most callers want; it never leaks the
/// block's local bindings back to the caller.
pub(super) fn exec_block_closure(
    nodes: &[Node],
    captured_env: &Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut throwaway = captured_env.clone();
    match exec_block_closure_into(nodes, &mut throwaway, functions, classes, enums, impl_methods) {
        // A `return` inside this block/BDD-it-block body (bug #188b) exits THIS
        // call, yielding the returned value as the block's own result — it must
        // not escape further as an error. See `CompileError::BlockReturn`.
        Err(CompileError::BlockReturn(value)) => Ok(value),
        other => other,
    }
}

/// Like `exec_block_closure`, but runs against `out_env` and, on normal
/// completion, writes the block's final bindings back into it. Lambda execution
/// uses this so a `me`-method's mutation to an object argument is observable for
/// write-back to the caller (control-flow exits — break/continue/return — do not
/// sync, matching their unwinding semantics). Identical statement handling to the
/// wrapper above, so DoBlock lambdas keep full block semantics.
pub(super) fn exec_block_closure_into(
    nodes: &[Node],
    out_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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
    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_call("<block>");
    }

    let mut local_env = out_env.clone();
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
                let global_name = if assign_stmt.op == simple_parser::ast::AssignOp::Assign {
                    match &assign_stmt.target {
                        simple_parser::ast::Expr::Identifier(name)
                            if MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name)) =>
                        {
                            Some(name.clone())
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                let control = if assign_stmt.op != simple_parser::ast::AssignOp::Assign {
                    exec_augmented_assignment(assign_stmt, &mut local_env, functions, classes, enums, impl_methods)
                } else {
                    exec_assignment(assign_stmt, &mut local_env, functions, classes, enums, impl_methods)
                }?;
                match control {
                    crate::interpreter::Control::Next => {
                        if let Some(name) = global_name {
                            if let Some(value) = local_env.remove(&name) {
                                MODULE_GLOBALS.with(|cell| {
                                    cell.borrow_mut().insert(name, value);
                                });
                            }
                        }
                        last_value = Value::Nil;
                    }
                    crate::interpreter::Control::Return(value) => return Ok(value),
                    crate::interpreter::Control::Break(value, _) => {
                        return Err(CompileError::LoopBreak(value));
                    }
                    crate::interpreter::Control::Continue(_) => {
                        return Err(CompileError::LoopContinue);
                    }
                }
                continue;
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
                    Value::Str(_) | Value::Symbol(_) => {
                        let name = match &context_obj {
                            Value::Str(name) => name.as_str(),
                            Value::Symbol(name) => name.as_str(),
                            _ => unreachable!(),
                        };
                        let name_str = if matches!(context_obj, Value::Symbol(_)) {
                            format!("with {}", name)
                        } else {
                            name.to_string()
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
                        // Non-BDD context: set context object for method dispatch
                        let var_name = if let Expr::Identifier(name) = &ctx_stmt.context {
                            Some(name.clone())
                        } else {
                            None
                        };

                        let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
                        let prev_var_name = CONTEXT_VAR_NAME.with(|cell| cell.borrow().clone());

                        CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));
                        CONTEXT_VAR_NAME.with(|cell| *cell.borrow_mut() = var_name.clone());

                        last_value = exec_block_closure(
                            &ctx_stmt.body.statements,
                            &local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;

                        // Persist mutations back to local env
                        if let Some(name) = &var_name {
                            if let Some(updated_obj) = CONTEXT_OBJECT.with(|cell| cell.borrow().clone()) {
                                local_env.insert(name.clone(), updated_obj);
                            }
                        }

                        CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);
                        CONTEXT_VAR_NAME.with(|cell| *cell.borrow_mut() = prev_var_name);
                    }
                }
            }
            Node::If(if_stmt) => {
                // `handled` tracks whether the main `if` (or its let-pattern) fired.
                // When it doesn't, we MUST walk `elif_branches` before the `else`
                // block — omitting them silently routed every `if/elif/else` chain
                // straight to `else` (mirror of the fix noted in `exec_if`).
                let mut handled = false;
                if let Some(pattern) = &if_stmt.let_pattern {
                    // `if val IDENT = expr:` is an optional-binding: only take the branch
                    // when the value is present, binding IDENT to the *unwrapped* value.
                    // Running a bare identifier pattern through `pattern_matches` always
                    // matches (even nil/None) and binds the Option wrapper itself — see
                    // `optional_let_binding`'s doc comment and bug #188a. Defer structural
                    // patterns (Some(x), enums, tuples, …) to `pattern_matches`.
                    let value = evaluate_expr(
                        &if_stmt.condition,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    match optional_let_binding(pattern, &value) {
                        LetBind::Bind(name, inner) => {
                            local_env.insert(name, inner);
                            last_value = exec_block_closure_mut(
                                &if_stmt.then_block.statements,
                                &mut local_env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?;
                            handled = true;
                        }
                        LetBind::Skip => {}
                        LetBind::NotApplicable => {
                            let mut bindings = std::collections::HashMap::new();
                            if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
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
                                handled = true;
                            }
                        }
                    }
                } else if {
                    let cond_val = evaluate_expr(
                        &if_stmt.condition,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    // `is_condition_present` (not plain `.truthy()`): see its
                    // doc comment in `interpreter_control.rs`.
                    is_condition_present(&if_stmt.condition, &cond_val)
                } {
                    last_value = exec_block_closure_mut(
                        &if_stmt.then_block.statements,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    handled = true;
                }
                if !handled {
                    for (pattern, cond, block) in &if_stmt.elif_branches {
                        if let Some(pattern) = pattern {
                            let value = evaluate_expr(cond, &mut local_env, functions, classes, enums, impl_methods)?;
                            match optional_let_binding(pattern, &value) {
                                LetBind::Bind(name, inner) => {
                                    local_env.insert(name, inner);
                                    last_value = exec_block_closure_mut(
                                        &block.statements,
                                        &mut local_env,
                                        functions,
                                        classes,
                                        enums,
                                        impl_methods,
                                    )?;
                                    handled = true;
                                    break;
                                }
                                LetBind::Skip => {}
                                LetBind::NotApplicable => {
                                    let mut bindings = std::collections::HashMap::new();
                                    if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                                        for (name, val) in bindings {
                                            local_env.insert(name, val);
                                        }
                                        last_value = exec_block_closure_mut(
                                            &block.statements,
                                            &mut local_env,
                                            functions,
                                            classes,
                                            enums,
                                            impl_methods,
                                        )?;
                                        handled = true;
                                        break;
                                    }
                                }
                            }
                        } else if {
                            let elif_val = evaluate_expr(cond, &mut local_env, functions, classes, enums, impl_methods)?;
                            is_condition_present(cond, &elif_val)
                        } {
                            last_value = exec_block_closure_mut(
                                &block.statements,
                                &mut local_env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?;
                            handled = true;
                            break;
                        }
                    }
                }
                if !handled {
                    if let Some(ref else_block) = if_stmt.else_block {
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
                let is_dict_iteration = matches!(&iterable, Value::Dict(_));
                'for_loop_own: for (index, val) in iter_values.into_iter().enumerate() {
                    let bind_value = if for_stmt.auto_enumerate && !is_dict_iteration {
                        Value::Tuple(vec![Value::Int(index as i64), val])
                    } else {
                        val
                    };
                    bind_pattern_value(&for_stmt.pattern, bind_value, false, &mut local_env);
                    match exec_block_closure_mut(
                        &for_stmt.body.statements,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    ) {
                        Ok(val) => last_value = val,
                        Err(CompileError::LoopBreak(val)) => {
                            last_value = val.unwrap_or(Value::Nil);
                            break 'for_loop_own;
                        }
                        Err(CompileError::LoopContinue) => continue 'for_loop_own,
                        Err(e) => return Err(e),
                    }
                }
            }
            Node::Match(match_stmt) => {
                let subject = evaluate_expr(
                    &match_stmt.subject,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                let mut matched = false;
                for arm in &match_stmt.arms {
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(&arm.pattern, &subject, &mut bindings, enums, classes)? {
                        if let Some(guard) = &arm.guard {
                            let mut guard_env = local_env.clone();
                            for (name, value) in &bindings {
                                guard_env.insert(name.clone(), value.clone());
                            }
                            let guard_val = evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                            if !is_condition_present(guard, &guard_val) {
                                continue;
                            }
                        }
                        for (name, value) in bindings {
                            local_env.insert(name, value);
                        }
                        last_value = exec_block_closure_mut(
                            &arm.body.statements,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    last_value = Value::Nil;
                }
            }
            Node::Function(f) => {
                // Handle function definitions inside block closures (like in `it` blocks)
                // Register in both local_env and functions map for recursive calls to work

                // Add to functions map so recursive calls can find it
                let arc_f = Arc::new(f.clone());
                functions.insert(f.name.clone(), Arc::clone(&arc_f));

                // Also add to local_env as a Function value with captured environment
                local_env.insert(
                    f.name.clone(),
                    Value::Function {
                        name: f.name.clone(),
                        def: arc_f,
                        captured_env: Arc::new(local_env.clone()), // Capture current scope
                    },
                );
                last_value = Value::Nil;
            }
            Node::Class(class_def) => {
                // Handle class definitions inside block closures (like in `it` blocks)
                // Inject mixin fields/methods before registration
                let final_class = inject_mixins(class_def);
                classes.insert(final_class.name.clone(), Arc::new(final_class.clone()));
                local_env.insert(
                    final_class.name.clone(),
                    Value::Constructor {
                        class_name: final_class.name.clone(),
                    },
                );
                // Register static methods as mangled free functions (ClassName__method)
                for method in &final_class.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", final_class.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }
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
                BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), Arc::new(e.clone())));
                // Also register in GLOBAL_ENUMS for cross-function enum visibility
                GLOBAL_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), Arc::new(e.clone())));
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
                    Arc::new(ClassDef {
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
                        is_value_type: true,
                    }),
                );
                // Register static methods as mangled free functions (StructName__method)
                for method in &s.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", s.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }
                last_value = Value::Nil;
            }
            Node::Class(c) => {
                let final_class = inject_mixins(c);
                classes.insert(final_class.name.clone(), Arc::new(final_class.clone()));
                local_env.insert(
                    final_class.name.clone(),
                    Value::Constructor {
                        class_name: final_class.name.clone(),
                    },
                );
                // Register static methods as mangled free functions (ClassName__method)
                for method in &final_class.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", final_class.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }
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
                        let mut combined_methods_bare = impl_block.methods.clone();
                        let impl_method_names: std::collections::HashSet<_> =
                            impl_block.methods.iter().map(|m| m.name.clone()).collect();

                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                combined_methods_bare.push(trait_method.clone());
                            }
                        }

                        let combined_methods_arc: Vec<Arc<FunctionDef>> =
                            combined_methods_bare.iter().map(|m| Arc::new(m.clone())).collect();

                        // Register in TRAIT_IMPLS with combined methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut()
                                .insert((trait_name.clone(), type_name.clone()), combined_methods_arc);
                        });

                        // Merge impl methods into ClassDef (mirrors interpreter_eval.rs:358-359)
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            Arc::make_mut(class_def).methods.extend(combined_methods_bare);
                        }
                    } else {
                        // Trait not found - just register the impl methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                impl_block.methods.iter().map(|m| Arc::new(m.clone())).collect(),
                            );
                        });

                        // Merge impl methods into ClassDef
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                        }
                    }
                } else {
                    // Non-trait impl block - merge methods into ClassDef
                    if let Some(class_def) = classes.get_mut(&type_name) {
                        Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                    }
                }

                // Register static methods from impl as mangled free functions (TypeName__method)
                for method in &impl_block.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", type_name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
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
                crate::interpreter::const_trace("blockexec:const-insert", &const_stmt.name); CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
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
                    crate::interpreter::const_trace("blockexec:static-insert", &static_stmt.name); CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
                }
                last_value = Value::Nil;
            }
            Node::While(while_stmt) => loop {
                if crate::interpreter::is_timeout_exceeded() {
                    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names.clone());
                    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars.clone());
                    return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
                }
                let cond = evaluate_expr(
                    &while_stmt.condition,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                if !is_condition_present(&while_stmt.condition, &cond) {
                    break;
                }
                match exec_block_closure_mut(
                    &while_stmt.body.statements,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                ) {
                    Ok(val) => last_value = val,
                    Err(CompileError::LoopBreak(val)) => {
                        last_value = val.unwrap_or(Value::Nil);
                        break;
                    }
                    Err(CompileError::LoopContinue) => continue,
                    Err(e) => return Err(e),
                }
            },
            Node::Loop(loop_stmt) => loop {
                if crate::interpreter::is_timeout_exceeded() {
                    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names.clone());
                    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars.clone());
                    return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
                }
                match exec_block_closure_mut(
                    &loop_stmt.body.statements,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                ) {
                    Ok(val) => last_value = val,
                    Err(CompileError::LoopBreak(val)) => {
                        last_value = val.unwrap_or(Value::Nil);
                        break;
                    }
                    Err(CompileError::LoopContinue) => continue,
                    Err(e) => return Err(e),
                }
            },
            Node::Break(b) => {
                let value = if let Some(expr) = &b.value {
                    Some(evaluate_expr(
                        expr,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?)
                } else {
                    None
                };
                CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
                IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
                return Err(CompileError::LoopBreak(value));
            }
            Node::Continue(_) => {
                CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
                IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
                return Err(CompileError::LoopContinue);
            }
            Node::Return(ret) => {
                // `return` inside a lambda/block-closure body must exit THIS body,
                // yielding the value to the body's own call boundary — not become
                // just the "value" of whatever if/match/loop statement it's nested
                // in (bug #188b). Mirror `Node::Break`/`Node::Continue` above: raise
                // a sentinel that propagates via `?` through nested
                // `exec_block_closure_mut` calls and is caught at the lambda/
                // block-closure/BDD call boundary (see `CompileError::BlockReturn`).
                let value = if let Some(expr) = &ret.value {
                    evaluate_expr(expr, &mut local_env, functions, classes, enums, impl_methods)?
                } else {
                    Value::Nil
                };
                CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
                IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
                return Err(CompileError::BlockReturn(value));
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    // Restore CONST_NAMES and IMMUTABLE_VARS before returning
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);
    // Propagate the block's final bindings so callers passing a mutable env (lambda
    // write-back) observe argument mutations. The throwaway-clone wrapper discards this.
    *out_env = local_env;
    Ok(last_value)
}

/// Execute statements in an already-existing mutable environment.
/// Used for if-let blocks and for loop bodies where assignments should propagate to the outer scope.
fn exec_block_closure_mut(
    nodes: &[Node],
    local_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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
                    // Use bind_pattern_value so typed (val x: T = ...), tuple, and
                    // array patterns bind here too — hand-rolling only the identifier
                    // forms silently dropped annotated bindings in nested closure blocks.
                    let is_mutable = let_stmt.mutability.is_mutable();
                    bind_pattern_value(&let_stmt.pattern, val, is_mutable, local_env);
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let control = if assign_stmt.op != simple_parser::ast::AssignOp::Assign {
                    exec_augmented_assignment(assign_stmt, local_env, functions, classes, enums, impl_methods)
                } else {
                    exec_assignment(assign_stmt, local_env, functions, classes, enums, impl_methods)
                }?;
                match control {
                    crate::interpreter::Control::Next => {
                        last_value = Value::Nil;
                    }
                    crate::interpreter::Control::Return(value) => return Ok(value),
                    crate::interpreter::Control::Break(value, _) => {
                        return Err(CompileError::LoopBreak(value));
                    }
                    crate::interpreter::Control::Continue(_) => {
                        return Err(CompileError::LoopContinue);
                    }
                }
                continue;
            }
            Node::If(if_stmt) => {
                // `handled` gates the `elif_branches` walk: when neither the main
                // `if` nor its let-pattern fires, every `elif` must be tried before
                // the `else` block (previously they were silently skipped).
                let mut handled = false;
                if let Some(pattern) = &if_stmt.let_pattern {
                    // See the `optional_let_binding` fix in the sibling `exec_block_closure_into`
                    // above (bug #188a) — `pattern_matches` alone always matches a bare
                    // identifier pattern, even against nil/None, so it must be tried first.
                    let value = evaluate_expr(&if_stmt.condition, local_env, functions, classes, enums, impl_methods)?;
                    match optional_let_binding(pattern, &value) {
                        LetBind::Bind(name, inner) => {
                            local_env.insert(name, inner);
                            last_value = exec_block_closure_mut(
                                &if_stmt.then_block.statements,
                                local_env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?;
                            handled = true;
                        }
                        LetBind::Skip => {}
                        LetBind::NotApplicable => {
                            let mut bindings = std::collections::HashMap::new();
                            if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
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
                                handled = true;
                            }
                        }
                    }
                } else if {
                    let cond_val = evaluate_expr(&if_stmt.condition, local_env, functions, classes, enums, impl_methods)?;
                    // `is_condition_present` (not plain `.truthy()`): see its
                    // doc comment in `interpreter_control.rs`.
                    is_condition_present(&if_stmt.condition, &cond_val)
                } {
                    last_value = exec_block_closure_mut(
                        &if_stmt.then_block.statements,
                        local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    handled = true;
                }
                if !handled {
                    for (pattern, cond, block) in &if_stmt.elif_branches {
                        if let Some(pattern) = pattern {
                            let value = evaluate_expr(cond, local_env, functions, classes, enums, impl_methods)?;
                            match optional_let_binding(pattern, &value) {
                                LetBind::Bind(name, inner) => {
                                    local_env.insert(name, inner);
                                    last_value = exec_block_closure_mut(
                                        &block.statements,
                                        local_env,
                                        functions,
                                        classes,
                                        enums,
                                        impl_methods,
                                    )?;
                                    handled = true;
                                    break;
                                }
                                LetBind::Skip => {}
                                LetBind::NotApplicable => {
                                    let mut bindings = std::collections::HashMap::new();
                                    if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                                        for (name, val) in bindings {
                                            local_env.insert(name, val);
                                        }
                                        last_value = exec_block_closure_mut(
                                            &block.statements,
                                            local_env,
                                            functions,
                                            classes,
                                            enums,
                                            impl_methods,
                                        )?;
                                        handled = true;
                                        break;
                                    }
                                }
                            }
                        } else if {
                            let elif_val = evaluate_expr(cond, local_env, functions, classes, enums, impl_methods)?;
                            is_condition_present(cond, &elif_val)
                        } {
                            last_value = exec_block_closure_mut(
                                &block.statements,
                                local_env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?;
                            handled = true;
                            break;
                        }
                    }
                }
                if !handled {
                    if let Some(ref else_block) = if_stmt.else_block {
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
                let is_dict_iteration = matches!(&iterable, Value::Dict(_));
                'for_loop: for (index, val) in iter_values.into_iter().enumerate() {
                    let bind_value = if for_stmt.auto_enumerate && !is_dict_iteration {
                        Value::Tuple(vec![Value::Int(index as i64), val])
                    } else {
                        val
                    };
                    bind_pattern_value(&for_stmt.pattern, bind_value, false, local_env);
                    match exec_block_closure_mut(
                        &for_stmt.body.statements,
                        local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    ) {
                        Ok(val) => last_value = val,
                        Err(CompileError::LoopBreak(val)) => {
                            last_value = val.unwrap_or(Value::Nil);
                            break 'for_loop;
                        }
                        Err(CompileError::LoopContinue) => continue 'for_loop,
                        Err(e) => return Err(e),
                    }
                }
            }
            Node::Match(match_stmt) => {
                let subject = evaluate_expr(&match_stmt.subject, local_env, functions, classes, enums, impl_methods)?;
                let mut matched = false;
                for arm in &match_stmt.arms {
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(&arm.pattern, &subject, &mut bindings, enums, classes)? {
                        if let Some(guard) = &arm.guard {
                            let mut guard_env = local_env.clone();
                            for (name, value) in &bindings {
                                guard_env.insert(name.clone(), value.clone());
                            }
                            let guard_val = evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                            if !is_condition_present(guard, &guard_val) {
                                continue;
                            }
                        }
                        for (name, value) in bindings {
                            local_env.insert(name, value);
                        }
                        last_value = exec_block_closure_mut(
                            &arm.body.statements,
                            local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    last_value = Value::Nil;
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
                BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), Arc::new(e.clone())));
                // Also register in GLOBAL_ENUMS for cross-function enum visibility
                GLOBAL_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), Arc::new(e.clone())));
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
                    Arc::new(ClassDef {
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
                        is_value_type: true,
                    }),
                );
                // Register static methods as mangled free functions (StructName__method)
                for method in &s.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", s.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }
                last_value = Value::Nil;
            }
            Node::Class(c) => {
                let final_class = inject_mixins(c);
                classes.insert(final_class.name.clone(), Arc::new(final_class.clone()));
                local_env.insert(
                    final_class.name.clone(),
                    Value::Constructor {
                        class_name: final_class.name.clone(),
                    },
                );
                // Register static methods as mangled free functions (ClassName__method)
                for method in &final_class.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", final_class.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }
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
                        let mut combined_methods_bare = impl_block.methods.clone();
                        let impl_method_names: std::collections::HashSet<_> =
                            impl_block.methods.iter().map(|m| m.name.clone()).collect();

                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                combined_methods_bare.push(trait_method.clone());
                            }
                        }

                        let combined_methods_arc: Vec<Arc<FunctionDef>> =
                            combined_methods_bare.iter().map(|m| Arc::new(m.clone())).collect();

                        // Register in TRAIT_IMPLS with combined methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut()
                                .insert((trait_name.clone(), type_name.clone()), combined_methods_arc);
                        });

                        // Merge impl methods into ClassDef (mirrors interpreter_eval.rs:358-359)
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            Arc::make_mut(class_def).methods.extend(combined_methods_bare);
                        }
                    } else {
                        // Trait not found - just register the impl methods
                        TRAIT_IMPLS.with(|cell| {
                            cell.borrow_mut().insert(
                                (trait_name.clone(), type_name.clone()),
                                impl_block.methods.iter().map(|m| Arc::new(m.clone())).collect(),
                            );
                        });

                        // Merge impl methods into ClassDef
                        if let Some(class_def) = classes.get_mut(&type_name) {
                            Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                        }
                    }
                } else {
                    // Non-trait impl block - merge methods into ClassDef
                    if let Some(class_def) = classes.get_mut(&type_name) {
                        Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                    }
                }

                // Register static methods from impl as mangled free functions (TypeName__method)
                for method in &impl_block.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", type_name, method.name);
                        let arc_method = Arc::new(method.clone());
                        functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        local_env.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(Env::new()),
                            },
                        );
                    }
                }

                last_value = Value::Nil;
            }
            Node::Const(const_stmt) => {
                // Evaluate const value
                let value = evaluate_expr(&const_stmt.value, local_env, functions, classes, enums, impl_methods)?;
                // Insert into environment
                local_env.insert(const_stmt.name.clone(), value);
                // Register as const name
                crate::interpreter::const_trace("blockexec:const-insert", &const_stmt.name); CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
                last_value = Value::Nil;
            }
            Node::Static(static_stmt) => {
                // Evaluate static value
                let value = evaluate_expr(&static_stmt.value, local_env, functions, classes, enums, impl_methods)?;
                // Insert into environment
                local_env.insert(static_stmt.name.clone(), value);
                // Register as const if immutable
                if !static_stmt.mutability.is_mutable() {
                    crate::interpreter::const_trace("blockexec:static-insert", &static_stmt.name); CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
                }
                last_value = Value::Nil;
            }
            Node::Function(f) => {
                // Handle function definitions inside mutable block closures
                // Register in both local_env and functions map for recursive calls to work

                // Add to functions map so recursive calls can find it
                let arc_f = Arc::new(f.clone());
                functions.insert(f.name.clone(), Arc::clone(&arc_f));

                // Also add to local_env as a Function value with captured environment
                local_env.insert(
                    f.name.clone(),
                    Value::Function {
                        name: f.name.clone(),
                        def: arc_f,
                        captured_env: Arc::new(local_env.clone()), // Capture current scope
                    },
                );
                last_value = Value::Nil;
            }
            Node::While(while_stmt) => loop {
                if crate::interpreter::is_timeout_exceeded() {
                    return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
                }
                let cond = evaluate_expr(
                    &while_stmt.condition,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                if !is_condition_present(&while_stmt.condition, &cond) {
                    break;
                }
                match exec_block_closure_mut(
                    &while_stmt.body.statements,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                ) {
                    Ok(val) => last_value = val,
                    Err(CompileError::LoopBreak(val)) => {
                        last_value = val.unwrap_or(Value::Nil);
                        break;
                    }
                    Err(CompileError::LoopContinue) => continue,
                    Err(e) => return Err(e),
                }
            },
            Node::Loop(loop_stmt) => loop {
                if crate::interpreter::is_timeout_exceeded() {
                    return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
                }
                match exec_block_closure_mut(
                    &loop_stmt.body.statements,
                    local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                ) {
                    Ok(val) => last_value = val,
                    Err(CompileError::LoopBreak(val)) => {
                        last_value = val.unwrap_or(Value::Nil);
                        break;
                    }
                    Err(CompileError::LoopContinue) => continue,
                    Err(e) => return Err(e),
                }
            },
            Node::Break(b) => {
                let value = if let Some(expr) = &b.value {
                    Some(evaluate_expr(expr, local_env, functions, classes, enums, impl_methods)?)
                } else {
                    None
                };
                return Err(CompileError::LoopBreak(value));
            }
            Node::Continue(_) => {
                return Err(CompileError::LoopContinue);
            }
            Node::Return(ret) => {
                // See the matching `Node::Return` arm in `exec_block_closure_into`
                // above (bug #188b) — propagate via the `BlockReturn` sentinel so a
                // `return` nested inside an if/match/loop body still exits the
                // whole enclosing lambda/block-closure body, not just this nested
                // call.
                let value = if let Some(expr) = &ret.value {
                    evaluate_expr(expr, local_env, functions, classes, enums, impl_methods)?
                } else {
                    Value::Nil
                };
                return Err(CompileError::BlockReturn(value));
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn object_identity(env: &Env) -> (*const HashMap<String, Value>, *const u8, usize, i64) {
        let Value::Array(slot) = env.get("slot").expect("slot") else {
            panic!("slot must be an array");
        };
        let Value::Object { fields, .. } = &slot[0] else {
            panic!("slot[0] must be an object");
        };
        let Value::Str(source) = fields.get("source").expect("source") else {
            panic!("source must be text");
        };
        let pos = fields.get("pos").expect("pos").as_int().expect("pos must be i64");
        (Arc::as_ptr(fields), source.as_ptr(), source.len(), pos)
    }

    #[test]
    fn closure_object_field_write_shares_source_buffer() {
        let mut parser =
            Parser::new("fn probe():\n    var loaded = slot[0]\n    loaded.pos = 1\n    slot[0] = loaded\n");
        let module = parser.parse().expect("parse probe");
        let body = module
            .items
            .iter()
            .find_map(|node| match node {
                Node::Function(function) if function.name == "probe" => Some(&function.body.statements),
                _ => None,
            })
            .expect("probe function");

        for source_len in [8, 1024 * 1024] {
            let mut fields = HashMap::new();
            fields.insert("source".to_string(), Value::text("x".repeat(source_len)));
            fields.insert("pos".to_string(), Value::Int(0));
            let object = Value::Object {
                class: "CoreLexerProbe".to_string(),
                fields: Arc::new(fields),
            };
            let mut env = Env::new();
            env.insert("slot".to_string(), Value::array(vec![object]));
            let before = object_identity(&env);

            exec_block_closure_into(
                body,
                &mut env,
                &mut HashMap::new(),
                &mut HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            )
            .expect("execute probe");

            let after = object_identity(&env);
            assert_eq!((after.2, after.3), (source_len, 1));
            assert_ne!(before.0, after.0, "field map must currently COW");
            assert_eq!(
                before.1, after.1,
                "source buffer must remain shared across field-map COW"
            );
        }
    }

    /// Parse `src` (must define `fn probe(): ...`) and return its body statements —
    /// used to drive `exec_block_closure`/`exec_block_closure_into` the same way a
    /// lambda/block-closure/BDD `it`-block body would be driven.
    fn parse_probe_body(src: &str) -> Vec<Node> {
        let mut parser = Parser::new(src);
        let module = parser.parse().expect("parse probe");
        module
            .items
            .iter()
            .find_map(|node| match node {
                Node::Function(function) if function.name == "probe" => Some(function.body.statements.clone()),
                _ => None,
            })
            .expect("probe function")
    }

    /// Bug #188a: `if val v = x:` inside a lambda/block-closure/BDD `it`-block
    /// body must skip the branch when `x` is absent (nil/None). This executor
    /// (`exec_block_closure_into`'s `Node::If` handling) had its own copy of the
    /// pre-fix `pattern_matches`-only logic — a bare identifier pattern always
    /// matches, even against nil — and never received the `optional_let_binding`
    /// fix landed for the statement-level `exec_if`.
    #[test]
    fn if_val_skips_when_absent_in_block_closure() {
        let body = parse_probe_body("fn probe():\n    if val v = x:\n        \"TAKEN\"\n    else:\n        \"SKIPPED\"\n");
        let mut env = Env::new();
        env.insert("x".to_string(), Value::Nil);
        let result = exec_block_closure(&body, &env, &mut HashMap::new(), &mut HashMap::new(), &HashMap::new(), &HashMap::new())
            .expect("exec_block_closure");
        assert_eq!(result.to_display_string(), "SKIPPED");
    }

    /// Companion case: a present value must still take the branch, bound to the
    /// (unwrapped) value.
    #[test]
    fn if_val_binds_when_present_in_block_closure() {
        let body = parse_probe_body("fn probe():\n    if val v = x:\n        v\n    else:\n        99\n");
        let mut env = Env::new();
        env.insert("x".to_string(), Value::Int(42));
        let result = exec_block_closure(&body, &env, &mut HashMap::new(), &mut HashMap::new(), &HashMap::new(), &HashMap::new())
            .expect("exec_block_closure");
        assert_eq!(result.as_int().expect("int"), 42);
    }

    /// Bug #188b: `return` inside a match arm nested in a lambda/block-closure
    /// body must exit THIS body with the returned value — not just become the
    /// match statement's "value" (discarded to Nil, since `Node::Return` wasn't
    /// even handled) while execution falls through to the next statement.
    #[test]
    fn return_inside_match_arm_exits_block_closure() {
        let body = parse_probe_body("fn probe():\n    match 1:\n        1: return 100\n    return 999\n");
        let env = Env::new();
        let result = exec_block_closure(&body, &env, &mut HashMap::new(), &mut HashMap::new(), &HashMap::new(), &HashMap::new())
            .expect("exec_block_closure");
        assert_eq!(result.as_int().expect("int"), 100);
    }

    /// Companion case: a bare top-level `return` (no match/if nesting) inside a
    /// block-closure body must also exit with its value, not fall through to
    /// `Value::Nil` via the generic wildcard arm.
    #[test]
    fn return_at_top_level_exits_block_closure() {
        let body = parse_probe_body("fn probe():\n    return 100\n");
        let env = Env::new();
        let result = exec_block_closure(&body, &env, &mut HashMap::new(), &mut HashMap::new(), &HashMap::new(), &HashMap::new())
            .expect("exec_block_closure");
        assert_eq!(result.as_int().expect("int"), 100);
    }
}
