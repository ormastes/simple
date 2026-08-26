// Node execution logic - statement and expression evaluation

use std::collections::HashMap;
use std::sync::Arc;
use simple_parser::ast::{AssignOp, BinOp, BitfieldDef, BitfieldField, ClassDef, Expr, FunctionDef, ImportTarget, Node, Type};
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{strict_mem_enabled, Env, Value};
use super::core_types::{
    Control, Enums, ImplMethods, get_identifier_name, get_pattern_name, is_immutable_by_pattern,
    visit_pattern_binding_names,
};
use super::async_support::await_value;
use super::expr::evaluate_expr;
use super::interpreter_helpers::{bind_pattern_value, handle_method_call_with_self_update, handle_functional_update};
use super::interpreter_control::{
    assert_stmt_failure, exec_if, exec_while, exec_loop, exec_for, exec_match, exec_context, exec_with,
    is_condition_present,
};
use super::interpreter_state::{mark_as_moved, BLOCK_SCOPED_ENUMS, CONST_NAMES, IMMUTABLE_VARS, MODULE_GLOBALS};
use super::coverage_helpers::{record_node_coverage, extract_node_location};
use crate::interpreter_unit::{is_unit_type, validate_unit_type, validate_unit_constraints};
use simple_runtime::debug;

/// Check if the watchdog timeout has been exceeded (single atomic load, negligible overhead).
macro_rules! check_timeout {
    () => {
        if crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded {
                timeout_secs: crate::interpreter::timeout_limit_secs(),
            });
        }
    };
}

pub(crate) fn exec_node(
    node: &Node,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Catch statement-level hangs (module init, deep call chains).
    check_timeout!();

    // COVERAGE: Record line execution for this statement
    if super::coverage_helpers::is_coverage_enabled() {
        record_node_coverage(node);
    }

    // DEBUG: Check if debugger wants to pause at this statement
    if debug::is_debug_active_fast() {
        if let Some((file, line, _col)) = extract_node_location(node) {
            let mut ds = debug::debug_state();
            if ds.active {
                let line32 = line as u32;
                ds.update_top_frame_location(line32, 0);
                if ds.should_stop(&file, line32) {
                    // Capture locals from current env for inspection
                    let locals: Vec<(String, String, String)> = env
                        .iter()
                        .take(50)
                        .map(|(k, v)| (k.clone(), format!("{:?}", v), v.type_name().to_string()))
                        .collect();
                    ds.set_top_frame_locals(locals);
                    ds.step_mode = debug::StepMode::Continue;
                }
            }
        }
    }

    match node {
        Node::Bitfield(bitfield) => {
            super::register_bitfield(bitfield);
            Ok(Control::Next)
        }
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
                // Borrowed, not cloned: this runs on EVERY execution of the
                // statement (per loop iteration), and a generic annotation such
                // as `Dict<text, i64>` is a Vec plus several Strings to clone.
                let type_annotation: Option<&Type> = match &let_stmt.ty {
                    Some(ty) => Some(ty),
                    None => match &let_stmt.pattern {
                        simple_parser::ast::Pattern::Typed { ty, .. } => Some(ty),
                        _ => None,
                    },
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
                let value = match type_annotation {
                    // Coerce to Value::UInt when the annotation is an unsigned integer type
                    // so subsequent arithmetic on the bound variable applies modulo-2^width
                    // wrap. See doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md.
                    Some(Type::Simple(type_name)) if matches!(type_name.as_str(), "u8" | "u16" | "u32" | "u64") => {
                        let width: u8 = match type_name.as_str() {
                            "u8" => 8,
                            "u16" => 16,
                            "u32" => 32,
                            "u64" => 64,
                            _ => unreachable!(),
                        };
                        match value {
                            // Already-typed UInt: keep as-is (literal-suffix path).
                            Value::UInt { .. } => value,
                            // Plain Int: wrap into UInt at the annotated width.
                            Value::Int(i) => {
                                let masked: u64 = match width {
                                    8 => (i as u8) as u64,
                                    16 => (i as u16) as u64,
                                    32 => (i as u32) as u64,
                                    64 => i as u64,
                                    _ => i as u64,
                                };
                                Value::UInt { value: masked, width }
                            }
                            // Other types pass through (e.g. Object newtypes around u32).
                            other => other,
                        }
                    }
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
                    Some(Type::Array {
                        size: Some(size_expr), ..
                    }) => {
                        // Fixed-size array: [T; N]
                        // Evaluate the size expression to get a concrete integer
                        let size_value = evaluate_expr(size_expr, env, functions, classes, enums, impl_methods)?;
                        let size = match size_value {
                            Value::Int(n) if n >= 0 => n as usize,
                            _ => {
                                let var_name = get_var_name(&let_stmt.pattern);
                                return Err(CompileError::semantic(format!(
                                    "Fixed-size array size must be a non-negative integer, got {:?}",
                                    size_value
                                )));
                            }
                        };

                        // Convert Array to FixedSizeArray
                        match value {
                            Value::Array(arc_data) => {
                                if arc_data.len() != size {
                                    let var_name = get_var_name(&let_stmt.pattern);
                                    return Err(CompileError::semantic(format!(
                                        "Fixed-size array `{}` size mismatch: expected {}, got {}",
                                        var_name,
                                        size,
                                        arc_data.len()
                                    )));
                                }
                                let data = Arc::unwrap_or_clone(arc_data);
                                Value::FixedSizeArray { size, data }
                            }
                            _ => {
                                let var_name = get_var_name(&let_stmt.pattern);
                                return Err(CompileError::semantic(format!(
                                    "Expected array for fixed-size array binding `{}`, got {:?}",
                                    var_name, value
                                )));
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
            } else if strict_mem_enabled() {
                // strict-mem (plan M5 §2): an initializer-less `let` binds no
                // value at all today — the name is indistinguishable from one
                // never declared, so a read can silently shadow-miss into an
                // unrelated enclosing/global/function binding. Mark the
                // pattern's name(s) uninit (no overlay entry) so a strict-mode
                // read traps before that fallback cascade runs.
                visit_pattern_binding_names(&let_stmt.pattern, &mut |name| {
                    env.mark_uninit(name);
                });
            }
            Ok(Control::Next)
        }
        Node::Const(const_stmt) => {
            // E1024 - Const Eval Failed
            let value =
                evaluate_expr(&const_stmt.value, env, functions, classes, enums, impl_methods).map_err(|e| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::CONST_EVAL_FAILED)
                        .with_help("constant expressions must be evaluable at compile time")
                        .with_note(format!(
                            "error occurred while evaluating constant `{}`",
                            const_stmt.name
                        ));
                    CompileError::semantic_with_context(
                        format!("failed to evaluate constant `{}`: {}", const_stmt.name, e),
                        ctx,
                    )
                })?;
            env.insert(const_stmt.name.clone(), value);
            crate::interpreter::const_trace("node_exec:const-insert", &const_stmt.name);
            CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
            Ok(Control::Next)
        }
        Node::Static(static_stmt) => {
            let value = evaluate_expr(&static_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(static_stmt.name.clone(), value);
            if !static_stmt.mutability.is_mutable() {
                crate::interpreter::const_trace("node_exec:static-insert", &static_stmt.name);
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
            Ok(Control::Break(value, b.label.clone()))
        }
        Node::Continue(c) => Ok(Control::Continue(c.label.clone())),
        Node::Assert(assert_stmt) => {
            // A bare `assert <cond>` inside a plain `fn` body reaches this
            // executor.  Without this arm it fell through to the catch-all at the
            // bottom of `exec_node` and did nothing at all — silently inert, so a
            // violated in-language contract check simply continued.  The
            // block-closure executors (`interpreter_call/block_execution.rs`) had
            // the same hole for lambda / BDD `it`-block bodies.
            let condition_value = evaluate_expr(&assert_stmt.condition, env, functions, classes, enums, impl_methods)?;
            if !is_condition_present(&assert_stmt.condition, &condition_value) {
                return Err(assert_stmt_failure(assert_stmt, &condition_value));
            }
            Ok(Control::Next)
        }
        Node::Pass(_) => Ok(Control::Next), // No-op, just continue to next statement
        Node::Defer(defer_stmt) => {
            // Defer statement: queue the body for execution when the current scope exits
            // The body is converted to a Block and queued via the tail injection mechanism
            use simple_parser::ast::{Block, DeferBody};
            use crate::r#macro::queue_tail_injection;

            let block = match &defer_stmt.body {
                DeferBody::Expr(expr) => {
                    // Convert single expression to a block with one statement
                    Block {
                        span: defer_stmt.span,
                        statements: vec![Node::Expression(expr.clone())],
                    }
                }
                DeferBody::Block(block) => block.clone(),
            };

            queue_tail_injection(block);
            Ok(Control::Next)
        }
        Node::ErrDefer(_errdefer_stmt) => {
            // Errdefer: only runs when scope exits with error.
            // In the Rust bootstrap interpreter, errdefer is registered but
            // error-conditional execution is handled by the Simple self-hosted compiler.
            // For bootstrap, treat as no-op (the self-hosted interpreter has full support).
            Ok(Control::Next)
        }
        Node::Guard(guard_stmt) => {
            // Guard clause: ? condition -> result
            // If condition is Some and true, or if condition is None (else), return the result
            let should_return = match &guard_stmt.condition {
                Some(cond_expr) => {
                    let cond = evaluate_expr(cond_expr, env, functions, classes, enums, impl_methods)?;
                    // `is_condition_present` (not plain `.truthy()`): see its
                    // doc comment in `interpreter_control.rs` -- an `.?`
                    // condition's presence must not be re-decided from the
                    // payload's truthiness (the "0 is falsy" landmine).
                    is_condition_present(cond_expr, &cond)
                }
                None => true, // `? else -> result` always matches
            };
            if should_return {
                let result = evaluate_expr(&guard_stmt.result, env, functions, classes, enums, impl_methods)?;
                Ok(Control::Return(result))
            } else {
                Ok(Control::Next)
            }
        }
        Node::Match(match_stmt) => exec_match(match_stmt, env, functions, classes, enums, impl_methods),
        Node::Context(ctx_stmt) => exec_context(ctx_stmt, env, functions, classes, enums, impl_methods),
        Node::With(with_stmt) => exec_with(with_stmt, env, functions, classes, enums, impl_methods),
        Node::Expression(expr) => {
            if let Expr::UnsafeBlock(nodes) = expr {
                let (flow, _) = super::exec_unsafe_block(nodes, env, functions, classes, enums, impl_methods)?;
                return Ok(flow);
            }
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
                    def: Arc::new(f.clone()),
                    captured_env: Arc::new(env.clone()), // Capture current scope
                },
            );
            Ok(Control::Next)
        }
        Node::LiteralFunction(lit_fn) => {
            // Register literal function for custom string suffix handling
            // This enables syntax like: "value"_suffix -> LiteralFn.call("value")
            use super::interpreter_state::{LITERAL_FUNCTIONS, LiteralFunctionInfo};
            LITERAL_FUNCTIONS.with(
                |cell: &std::cell::RefCell<std::collections::HashMap<String, LiteralFunctionInfo>>| {
                    cell.borrow_mut().insert(
                        lit_fn.suffix.clone(),
                        LiteralFunctionInfo {
                            suffix: lit_fn.suffix.clone(),
                            return_type: lit_fn.return_type.clone(),
                            param_name: lit_fn.param_name.clone(),
                            body: lit_fn.body.clone(),
                        },
                    );
                },
            );
            Ok(Control::Next)
        }
        Node::Struct(s) => {
            // Register struct constructor in local scope
            env.insert(
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
                    env.insert(
                        mangled.clone(),
                        Value::Function {
                            name: mangled,
                            def: arc_method,
                            captured_env: Arc::new(Env::new()),
                        },
                    );
                }
            }
            Ok(Control::Next)
        }
        Node::Class(c) => {
            // Register class constructor in local scope
            classes.insert(c.name.clone(), Arc::new(c.clone()));
            env.insert(
                c.name.clone(),
                Value::Constructor {
                    class_name: c.name.clone(),
                },
            );
            // Register static methods as mangled free functions (ClassName__method)
            for method in &c.methods {
                let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                if is_static {
                    let mangled = format!("{}__{}", c.name, method.name);
                    let arc_method = Arc::new(method.clone());
                    functions.insert(mangled.clone(), Arc::clone(&arc_method));
                    env.insert(
                        mangled.clone(),
                        Value::Function {
                            name: mangled,
                            def: arc_method,
                            captured_env: Arc::new(Env::new()),
                        },
                    );
                }
            }
            Ok(Control::Next)
        }
        Node::Newtype(nt) => {
            // Newtype `Name = T` is lowered to an internal class `Name { value: T }`.
            // Constructor `Name(value: x)` and field access `.value` then route through
            // the existing class machinery. Operators on the wrapped value still need
            // dunder dispatch — handled separately if/when added.
            let synth_field = simple_parser::ast::Field {
                span: nt.span,
                name: "value".to_string(),
                ty: nt.inner_type.clone(),
                default: None,
                mutability: simple_parser::ast::Mutability::Immutable,
                visibility: simple_parser::ast::Visibility::Public,
                bit_width: None,
            };
            let synth_class = ClassDef {
                span: nt.span,
                name: nt.name.clone(),
                generic_params: Vec::new(),
                where_clause: vec![],
                fields: vec![synth_field],
                methods: vec![],
                parent: None,
                visibility: nt.visibility,
                effects: Vec::new(),
                attributes: Vec::new(),
                doc_comment: nt.doc_comment.clone(),
                invariant: None,
                macro_invocations: vec![],
                mixins: vec![],
                is_generic_template: false,
                specialization_of: None,
                type_bindings: std::collections::HashMap::new(),
                is_value_type: false,
            };
            classes.insert(nt.name.clone(), Arc::new(synth_class));
            env.insert(
                nt.name.clone(),
                Value::Constructor {
                    class_name: nt.name.clone(),
                },
            );
            Ok(Control::Next)
        }
        Node::Enum(e) => {
            // Register enum type in local scope via thread-local
            BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow_mut().insert(e.name.clone(), Arc::new(e.clone())));
            env.insert(
                e.name.clone(),
                Value::EnumType {
                    enum_name: e.name.clone(),
                },
            );
            // Register enum static methods as mangled free functions
            for method in &e.methods {
                let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                if is_static {
                    let mangled = format!("{}__{}", e.name, method.name);
                    let arc_method = Arc::new(method.clone());
                    functions.insert(mangled.clone(), Arc::clone(&arc_method));
                    env.insert(
                        mangled.clone(),
                        Value::Function {
                            name: mangled,
                            def: arc_method,
                            captured_env: Arc::new(Env::new()),
                        },
                    );
                }
            }
            Ok(Control::Next)
        }
        // A `use` written inside a function body or any block. Without this arm
        // it falls into the catch-all below, which silently returns
        // `Control::Next`: the statement parses, nothing is registered, and the
        // imported symbol never enters scope. The call site then fails with a
        // "function not found" naming the CALLEE rather than the import, which
        // reads as a missing or unexported function and has misdiagnosed this
        // bug repeatedly. Module-scope `use` was always handled (in
        // interpreter_eval); only this block-scoped position was missing, which
        // left real stdlib code (e.g. std.crypto.sha1, whose body-scoped
        // imports never resolved) unable to run at all.
        // See doc/08_tracking/bug/block_scoped_use_no_op_symbol_resolution_2026-08-18.md
        Node::UseStmt(use_stmt) => {
            let current_file = super::get_current_file();
            // `enums` is borrowed immutably in this signature; enum imports
            // reach the interpreter through the GLOBAL_ENUMS thread-local
            // rather than this map, so a local copy satisfies the loader
            // without dropping them.
            let mut merged_enums = enums.clone();
            let loaded = crate::interpreter::interpreter_module::load_and_merge_module(
                use_stmt,
                current_file.as_deref(),
                functions,
                classes,
                &mut merged_enums,
            )?;
            if let Value::Dict(exports) = &loaded {
                // Same unpack rules as module scope: Group binds only the named
                // items, Glob binds everything, Single/Aliased bind the module
                // dict and unpack nothing.
                let mut bindings: Vec<(String, Value)> = Vec::new();
                match &use_stmt.target {
                    ImportTarget::Group(items) => {
                        for item_target in items {
                            match item_target {
                                ImportTarget::Single(name) => {
                                    if let Some(v) = exports.get(name) {
                                        bindings.push((name.clone(), v.clone()));
                                    }
                                }
                                ImportTarget::Aliased { name, alias } => {
                                    if let Some(v) = exports.get(name) {
                                        bindings.push((alias.clone(), v.clone()));
                                    }
                                }
                                // Nested groups are unsupported at module scope
                                // too; stay consistent rather than inventing a
                                // rule here.
                                _ => {}
                            }
                        }
                    }
                    ImportTarget::Glob => {
                        for (name, value) in exports.iter() {
                            // Never glob-import `main`: it would be picked up by
                            // the entry-point fallback and run instead of the
                            // script's own main. Same guard as module scope. A
                            // NAMED import of `main` is an explicit opt-in and
                            // is deliberately not filtered.
                            if matches!(value, Value::Function { .. }) && name == "main" {
                                continue;
                            }
                            bindings.push((name.clone(), value.clone()));
                        }
                    }
                    ImportTarget::Single(_) | ImportTarget::Aliased { .. } => {}
                }
                for (name, value) in bindings {
                    if let Value::Function { def, .. } = &value {
                        functions.insert(name.clone(), Arc::clone(def));
                    }
                    env.insert(name.clone(), value.clone());
                    MODULE_GLOBALS.with(|cell| {
                        cell.borrow_mut().insert(name, value);
                    });
                }
            }
            Ok(Control::Next)
        }
        _ => Ok(Control::Next),
    }
}

// Helper function for regular assignment
pub(crate) fn exec_assignment(
    assign: &simple_parser::ast::AssignmentStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    if let Expr::Identifier(name) = &assign.target {
        // Check if this is a first-time assignment (implicit declaration)
        let is_first_assignment = !env.contains_key(name);

        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            crate::interpreter::const_trace("node_exec:enforce-const-hit", name);
            return Err(crate::error::factory::cannot_assign_to_const(name));
        }

        // Inside a method body, a bare `field = value` (no `self.`) would fall
        // through to the implicit-declaration path below and mint a *fresh
        // local* that shadows the receiver's field, leaving `self.field`
        // untouched -- a silent wrong result. Every other lane already rejects
        // this shape (HIR lowering: "unresolved name", MIR lowering:
        // "assignment target has no local binding", native codegen: "llvm
        // global store referenced undeclared symbol"), and the pure-Simple
        // interpreter errors with "undefined variable"; only this AST
        // interpreter silently no-opped. Reject it here so the trap is loud
        // and the engines agree. Note the read path already errors (E1001),
        // so this only restores read/write symmetry.
        // See doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md
        if is_first_assignment {
            if let Some(Value::Object { class, fields }) = env.get("self") {
                if fields.contains_key(name) {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_ASSIGNMENT)
                        .with_help(format!(
                            "write `self.{name} = ...` to assign the field; `self` is implicit only in the parameter list, not in field access"
                        ));
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "invalid assignment: `{name}` is a field of `{class}`; a bare `{name} = ...` creates a new local and leaves `self.{name}` unchanged"
                        ),
                        ctx,
                    ));
                }
            }
        }

        // Check immutability for reassignments (not first assignment)
        if !is_first_assignment {
            let is_immutable = IMMUTABLE_VARS.with(|cell| cell.borrow().contains(name));
            if is_immutable && !name.ends_with('_') {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help(format!(
                    "consider using '{name}_' for a mutable variable, or use '{name}->method()' for functional updates"
                ));
                return Err(CompileError::semantic_with_context(
                    format!("invalid assignment: cannot reassign to immutable variable '{}'", name),
                    ctx,
                ));
            }
        }

        // Fast path: `arr = arr + [e1, e2, ...]` on a Value::Array — push elements
        // in place instead of allocating a fresh array and copying both sides.
        // Mirrors the `arr += [..]` AugAssign fast path so the plain-assign form
        // has the same amortized O(N) behavior. See `try_array_append_in_place`.
        // Also handles `s = s + rhs` on Value::Str via try_string_append_in_place.
        if let Expr::Binary {
            op: BinOp::Add,
            left,
            right,
        } = &assign.value
        {
            if let Expr::Identifier(lname) = left.as_ref() {
                if lname == name {
                    let items: Option<&[Expr]> = match right.as_ref() {
                        Expr::Array(v) | Expr::VecLiteral(v) => Some(v.as_slice()),
                        _ => None,
                    };
                    if let Some(items) = items {
                        if try_array_append_in_place(name, items, env, functions, classes, enums, impl_methods)? {
                            // Also sync to MODULE_GLOBALS if this name lives there.
                            MODULE_GLOBALS.with(|cell| {
                                // Peek before taking the write borrow: `borrow_mut()` on this
                                // generation-tracked cell invalidates every owned-env template,
                                // and this path runs on EVERY local assignment. Until 2026-08-21
                                // that made each intra-module call rebuild its env (~5 ms in a
                                // driver module) -- see bootstrap_main_native_build_stalls_after_source_closure_2026-08-21.md
                                if !cell.borrow().contains_key(name) {
                                    return;
                                }
                                if let Some(v) = env.get(name) {
                                    cell.borrow_mut().insert(name.clone(), v.clone());
                                }
                                });
                            return Ok(Control::Next);
                        }
                    }
                    // String fast path: `s = s + rhs` where LHS is a Value::Str
                    // and RHS evaluates to a Value::Str. If the helper returns
                    // None, the in-place append fired. If it returns Some(val),
                    // the RHS wasn't a string — but we've still evaluated it
                    // exactly once, so complete the plain assignment using the
                    // value to preserve side-effect ordering with the slow path.
                    if matches!(env.get(name), Some(Value::Str(_))) {
                        match try_string_append_in_place(
                            name,
                            right.as_ref(),
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )? {
                            None => {
                                MODULE_GLOBALS.with(|cell| {
                                    // Peek before taking the write borrow: `borrow_mut()` on this
                                    // generation-tracked cell invalidates every owned-env template,
                                    // and this path runs on EVERY local assignment. Until 2026-08-21
                                    // that made each intra-module call rebuild its env (~5 ms in a
                                    // driver module) -- see bootstrap_main_native_build_stalls_after_source_closure_2026-08-21.md
                                    if !cell.borrow().contains_key(name) {
                                        return;
                                    }
                                    if let Some(v) = env.get(name) {
                                        cell.borrow_mut().insert(name.clone(), v.clone());
                                    }
                                    });
                                return Ok(Control::Next);
                            }
                            Some(rhs_val) => {
                                // Non-string RHS: fall back to generic `lhs + rhs`.
                                // LHS is still the Value::Str that was there before.
                                // Compute `lhs + rhs_val` using the binary op evaluator
                                // via a temporary variable binding so side effects of
                                // the RHS don't run twice.
                                let temp_name = "__plain_rhs_temp__".to_string();
                                env.insert(temp_name.clone(), rhs_val);
                                let binary_expr = Expr::Binary {
                                    op: BinOp::Add,
                                    left: Box::new(Expr::Identifier(name.clone())),
                                    right: Box::new(Expr::Identifier(temp_name.clone())),
                                };
                                let result = evaluate_expr(&binary_expr, env, functions, classes, enums, impl_methods)?;
                                env.remove(&temp_name);
                                env.insert(name.clone(), result);
                                MODULE_GLOBALS.with(|cell| {
                                    // Peek before taking the write borrow: `borrow_mut()` on this
                                    // generation-tracked cell invalidates every owned-env template,
                                    // and this path runs on EVERY local assignment. Until 2026-08-21
                                    // that made each intra-module call rebuild its env (~5 ms in a
                                    // driver module) -- see bootstrap_main_native_build_stalls_after_source_closure_2026-08-21.md
                                    if !cell.borrow().contains_key(name) {
                                        return;
                                    }
                                    if let Some(v) = env.get(name) {
                                        cell.borrow_mut().insert(name.clone(), v.clone());
                                    }
                                    });
                                return Ok(Control::Next);
                            }
                        }
                    }
                }
            }
        }

        // Handle method calls on objects - need to persist mutations to self
        let (value, update) =
            handle_method_call_with_self_update(&assign.value, env, functions, classes, enums, impl_methods)?;
        // Apply side effects from 'me' methods to the receiver object
        // But always do the explicit assignment - the user's assignment takes precedence
        if let Some((ref obj_name, ref new_self)) = update {
            // Only apply side effect if the receiver is different from the target
            // If they're the same, the assignment below will set the correct value
            if obj_name != name {
                env.insert(obj_name.clone(), new_self.clone());
            }
        }
        {
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
                            crate::interpreter::const_trace("node_exec:implicit-caps-insert", name);
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
                    // Peek first (see the note above): an unconditional borrow_mut here
                    // bumped the globals generation on every local assignment.
                    if !cell.borrow().contains_key(name) {
                        return;
                    }
                    cell.borrow_mut().insert(name.clone(), env.get(name).unwrap().clone());
                    });
            }
        }
        Ok(Control::Next)
    } else if let Expr::FieldAccess { receiver, field } = &assign.target {
        // Handle field assignment: obj.field = value
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        // Get the object name (must be an identifier for now)
        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            if let Some(obj_val) = env.remove(obj_name) {
                match obj_val {
                    Value::ClassInstance(instance) => {
                        instance.set_field(field.clone(), value);
                        env.insert(obj_name.clone(), Value::ClassInstance(instance));
                    }
                    Value::Object { class, mut fields } => {
                        {
                            let bf_check = Value::Object {
                                class: class.clone(),
                                fields: Arc::clone(&fields),
                            };
                            if let Some(updated) = super::update_bitfield_field(&bf_check, field, value.clone()) {
                                env.insert(obj_name.clone(), updated);
                                return Ok(Control::Next);
                            }
                        }
                        Arc::make_mut(&mut fields).insert(field.clone(), value);
                        env.insert(obj_name.clone(), Value::Object { class, fields });
                    }
                    other => {
                        env.insert(obj_name.clone(), other);
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("field assignment requires an object with mutable access");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "invalid assignment: cannot assign field on non-object value (obj `{}`, field `{}`)",
                                obj_name, field
                            ),
                            ctx,
                        ));
                    }
                }
                Ok(Control::Next)
            } else {
                let global_obj = MODULE_GLOBALS.with(|cell| cell.borrow().get(obj_name).cloned());
                if let Some(obj_val) = global_obj {
                    match obj_val {
                        Value::ClassInstance(instance) => {
                            instance.set_field(field.clone(), value);
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut()
                                    .insert(obj_name.clone(), Value::ClassInstance(instance));
                            });
                            Ok(Control::Next)
                        }
                        Value::Object { class, mut fields } => {
                            {
                                let bf_check = Value::Object {
                                    class: class.clone(),
                                    fields: Arc::clone(&fields),
                                };
                                if let Some(updated) = super::update_bitfield_field(&bf_check, field, value.clone()) {
                                    MODULE_GLOBALS.with(|cell| {
                                        cell.borrow_mut().insert(obj_name.clone(), updated);
                                    });
                                    return Ok(Control::Next);
                                }
                            }
                            Arc::make_mut(&mut fields).insert(field.clone(), value);
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut()
                                    .insert(obj_name.clone(), Value::Object { class, fields });
                            });
                            Ok(Control::Next)
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_ASSIGNMENT)
                                .with_help("field assignment requires an object with mutable access");
                            Err(CompileError::semantic_with_context(
                                format!("invalid assignment: cannot assign field on non-object value (obj `{}`, field `{}`)", obj_name, field),
                                ctx,
                            ))
                        }
                    }
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
            }
        }
        // Case 2: Indexed object field: arr[index].field = value
        else if let Expr::Index {
            receiver: array_expr,
            index,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(array_name) = array_expr.as_ref() {
                let index_value = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
                let idx = index_value.as_int()? as usize;
                if let Some(Value::Array(mut values)) = env.get(array_name).cloned() {
                    let items = Arc::make_mut(&mut values);
                    if idx >= items.len() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("check that the array index is in bounds");
                        return Err(CompileError::semantic_with_context(
                            format!("invalid assignment: array index {} is out of bounds", idx),
                            ctx,
                        ));
                    }
                    match items[idx].clone() {
                        Value::ClassInstance(instance) => {
                            instance.set_field(field.clone(), value);
                            items[idx] = Value::ClassInstance(instance);
                            env.insert(array_name.clone(), Value::Array(values));
                            Ok(Control::Next)
                        }
                        Value::Object { class, mut fields } => {
                            Arc::make_mut(&mut fields).insert(field.clone(), value);
                            items[idx] = Value::Object { class, fields };
                            env.insert(array_name.clone(), Value::Array(values));
                            Ok(Control::Next)
                        }
                        other => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_ASSIGNMENT)
                                .with_help("indexed field assignment requires an object element");
                            Err(CompileError::semantic_with_context(
                                format!(
                                    "invalid assignment: cannot set field on {} array element",
                                    other.type_name()
                                ),
                                ctx,
                            ))
                        }
                    }
                } else {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_ASSIGNMENT)
                        .with_help("indexed field assignment requires an array identifier");
                    Err(CompileError::semantic_with_context(
                        "invalid assignment: indexed field receiver is not an array",
                        ctx,
                    ))
                }
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help("indexed field assignment requires a simple array identifier");
                Err(CompileError::semantic_with_context(
                    "invalid assignment: complex indexed field receiver is not supported",
                    ctx,
                ))
            }
        }
        // Case 3: Nested field access: obj.inner.field = value
        else if let Expr::FieldAccess {
            receiver: inner_receiver,
            field: inner_field,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(obj_name) = inner_receiver.as_ref() {
                if let Some(obj_val) = env.remove(obj_name) {
                    match obj_val {
                        Value::Object { class, mut fields } => {
                            // Get the inner object
                            if let Some(inner_val) = fields.get(inner_field).cloned() {
                                match inner_val {
                                    Value::Object {
                                        class: inner_class,
                                        fields: inner_fields,
                                    } => {
                                        // Set the field on the inner object
                                        let mut inner_fields = inner_fields;
                                        Arc::make_mut(&mut inner_fields).insert(field.clone(), value);
                                        // Update the inner object in the outer object
                                        Arc::make_mut(&mut fields).insert(
                                            inner_field.clone(),
                                            Value::Object {
                                                class: inner_class,
                                                fields: inner_fields,
                                            },
                                        );
                                        // Update the outer object in env
                                        env.insert(obj_name.clone(), Value::Object { class, fields });
                                        Ok(Control::Next)
                                    }
                                    _ => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::INVALID_ASSIGNMENT)
                                            .with_help("nested field assignment requires inner value to be an object");
                                        Err(CompileError::semantic_with_context(
                                            format!(
                                                "invalid assignment: cannot assign field '{}' on non-object field '{}'",
                                                field, inner_field
                                            ),
                                            ctx,
                                        ))
                                    }
                                }
                            } else {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("check the field name");
                                Err(CompileError::semantic_with_context(
                                    format!("field '{}' not found on object", inner_field),
                                    ctx,
                                ))
                            }
                        }
                        // Class instances (`self` inside methods, any class-typed
                        // variable) use shared interior mutability: mutate the
                        // inner value through the instance's field lock.
                        Value::ClassInstance(instance) => {
                            let inner_val = instance.field(inner_field);
                            let result = match inner_val {
                                Some(Value::ClassInstance(inner_inst)) => {
                                    inner_inst.set_field(field.clone(), value);
                                    Ok(Control::Next)
                                }
                                Some(Value::Object {
                                    class: inner_class,
                                    fields: inner_fields,
                                }) => {
                                    let mut inner_fields = inner_fields;
                                    Arc::make_mut(&mut inner_fields).insert(field.clone(), value);
                                    instance.set_field(
                                        inner_field.clone(),
                                        Value::Object {
                                            class: inner_class,
                                            fields: inner_fields,
                                        },
                                    );
                                    Ok(Control::Next)
                                }
                                Some(_) => {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::INVALID_ASSIGNMENT)
                                        .with_help("nested field assignment requires inner value to be an object");
                                    Err(CompileError::semantic_with_context(
                                        format!(
                                            "invalid assignment: cannot assign field '{}' on non-object field '{}'",
                                            field, inner_field
                                        ),
                                        ctx,
                                    ))
                                }
                                None => {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::UNDEFINED_FIELD)
                                        .with_help("check the field name");
                                    Err(CompileError::semantic_with_context(
                                        format!("field '{}' not found on object", inner_field),
                                        ctx,
                                    ))
                                }
                            };
                            env.insert(obj_name.clone(), Value::ClassInstance(instance));
                            result
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_ASSIGNMENT)
                                .with_help("nested field assignment requires an object");
                            Err(CompileError::semantic_with_context(
                                format!("invalid assignment: cannot assign field on non-object value (obj `{}`, field `{}`)", obj_name, field),
                                ctx,
                            ))
                        }
                    }
                } else {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("check that the variable is defined and in scope");
                    Err(CompileError::semantic_with_context(
                        format!("variable '{}' not found", obj_name),
                        ctx,
                    ))
                }
            } else {
                // Deeper than the hand-written two-level cases (e.g.
                // `a.b.c.d = v`, `a[i].b.c = v`). Resolve the general place and
                // write through it. This is what used to be rejected with
                // "deeply nested field access requires intermediate variables".
                if let Some(place) =
                    super::place::resolve_place(&assign.target, env, functions, classes, enums, impl_methods)?
                {
                    if super::place::write_place(env, &place, value) {
                        return Ok(Control::Next);
                    }
                }
                let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                    "the assignment target is not a writable place; check that every field and index on the path exists",
                );
                Err(CompileError::semantic_with_context(
                    "invalid assignment: nested field assignment target is not a writable place",
                    ctx,
                ))
            }
        } else {
            // The object of the field access is neither an identifier nor a
            // simple nested field/index access. It may still be a place
            // (arbitrary projection chains are supported); only genuine
            // temporaries fall through to the error.
            if let Some(place) =
                super::place::resolve_place(&assign.target, env, functions, classes, enums, impl_methods)?
            {
                if super::place::write_place(env, &place, value) {
                    return Ok(Control::Next);
                }
            }
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help("field assignment requires a place: a variable followed by field/index projections");
            Err(CompileError::semantic_with_context(
                "invalid assignment: field assignment target is not a place",
                ctx,
            ))
        }
    } else if let Expr::Index { receiver, index } = &assign.target {
        // Handle index assignment: arr[i] = value or dict["key"] = value or self.dict[key] = value
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        let index_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;

        // Case 1: Plain identifier: arr[i] = value
        if let Expr::Identifier(container_name) = receiver.as_ref() {
            // Fast in-place path for a local array/dict that is PROVABLY
            // unaliased (Arc strong_count == 1, no weak refs): mutate in place,
            // avoiding the O(n) copy-on-write clone the `.cloned()` path below
            // performs on every element write. When the container is shared
            // (another variable aliases it) we fall through to the clone path,
            // preserving value semantics. Globals/tuples/__setitem__ also fall
            // through.
            let case1_unique = match env.get(container_name) {
                Some(Value::Array(arc)) => Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0,
                Some(Value::Dict(arc)) => Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0,
                _ => false,
            };
            if case1_unique {
                if let Some(slot) = env.get_mut(container_name) {
                    match slot {
                        Value::Array(arc) => {
                            if let Some(arr) = Arc::get_mut(arc) {
                                let idx = index_val.as_int()? as usize;
                                if idx < arr.len() {
                                    arr[idx] = value;
                                } else {
                                    while arr.len() < idx {
                                        arr.push(Value::Nil);
                                    }
                                    arr.push(value);
                                }
                                return Ok(Control::Next);
                            }
                        }
                        Value::Dict(dict) => {
                            if let Some(map) = Arc::get_mut(dict) {
                                map.insert(index_val.to_key_string(), Value::wrap_dict_entry(&index_val, value));
                                return Ok(Control::Next);
                            }
                        }
                        _ => {}
                    }
                }
            }
            // Try local env first
            let container_opt = env.get(container_name).cloned();
            // Try module globals if not in local env
            let is_global = container_opt.is_none();
            let container = if let Some(c) = container_opt {
                Some(c)
            } else {
                MODULE_GLOBALS.with(|cell| cell.borrow().get(container_name).cloned())
            };

            if let Some(container) = container {
                let new_container = match container {
                    Value::Array(mut arc) => {
                        let arr = Arc::make_mut(&mut arc);
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
                        Value::Array(arc)
                    }
                    Value::Dict(mut dict) => {
                        let key = index_val.to_key_string();
                        let stored = Value::wrap_dict_entry(&index_val, value);
                        Arc::make_mut(&mut dict).insert(key, stored);
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
                                format!(
                                    "index out of bounds: tuple index {} out of bounds (len={})",
                                    idx,
                                    tup.len()
                                ),
                                ctx,
                            ));
                        }
                    }
                    // __setitem__ dispatch for Object types (e.g., GpuBuffer, List)
                    Value::Object {
                        ref class, ref fields, ..
                    } => {
                        let setitem_method = classes
                            .get(class.as_str())
                            .and_then(|cd| cd.methods.iter().find(|m| m.name == "__setitem__").cloned())
                            .map(Arc::new)
                            .or_else(|| {
                                impl_methods
                                    .get(class.as_str())
                                    .and_then(|ms| ms.iter().find(|m| m.name == "__setitem__").cloned())
                            });
                        if let Some(method) = setitem_method {
                            let self_ctx = Some((class.as_str(), fields));
                            crate::interpreter::interpreter_call::exec_function_with_values_and_self(
                                &method,
                                &[index_val, value],
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                                self_ctx,
                            )?;
                            // Re-read the container to get updated self (me methods mutate)
                            // For mutable methods (me), the object may have been updated in env
                            container.clone()
                        } else {
                            let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                                "index assignment requires an array, dict, tuple, or object with __setitem__",
                            );
                            return Err(CompileError::semantic_with_context(
                                format!(
                                    "invalid assignment: cannot index assign value of type {}",
                                    container.type_name()
                                ),
                                ctx,
                            ));
                        }
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("index assignment requires an array, dict, tuple, or object with __setitem__");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "invalid assignment: cannot index assign value of type {}",
                                container.type_name()
                            ),
                            ctx,
                        ));
                    }
                };

                // Update the correct storage
                if is_global {
                    MODULE_GLOBALS.with(|cell| {
                        cell.borrow_mut().insert(container_name.clone(), new_container);
                    });
                } else {
                    env.insert(container_name.clone(), new_container);
                }
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
        }
        // Case 2: Field access: self.dict[key] = value or obj.arr[i] = value
        else if let Expr::FieldAccess {
            receiver: obj_expr,
            field: field_name,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(obj_name) = obj_expr.as_ref() {
                // Fast in-place path for the hot `self.buf[i] = color` raster
                // loop: mutate the field array in place only when it is PROVABLY
                // unaliased (Arc strong_count == 1, checked again via
                // Arc::get_mut), avoiding the O(n) clone the `.cloned()` path
                // below does on every write. A shared array (e.g. captured by
                // another variable) falls through to the clone path, preserving
                // value semantics.
                let case2_unique = match env.get(obj_name) {
                    Some(Value::Object { fields, .. }) => match fields.get(field_name) {
                        Some(Value::Array(arc)) => Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0,
                        Some(Value::Dict(arc)) => Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0,
                        _ => false,
                    },
                    _ => false,
                };
                if case2_unique {
                    if let Some(Value::Object { fields, .. }) = env.get_mut(obj_name) {
                        if let Some(fmap) = Arc::get_mut(fields) {
                            if let Some(slot) = fmap.get_mut(field_name) {
                                match slot {
                                    Value::Array(arc) => {
                                        if let Some(arr) = Arc::get_mut(arc) {
                                            let idx = index_val.as_int()? as usize;
                                            if idx < arr.len() {
                                                arr[idx] = value;
                                            } else {
                                                while arr.len() < idx {
                                                    arr.push(Value::Nil);
                                                }
                                                arr.push(value);
                                            }
                                            return Ok(Control::Next);
                                        }
                                    }
                                    Value::Dict(dict) => {
                                        if let Some(map) = Arc::get_mut(dict) {
                                            map.insert(
                                                index_val.to_key_string(),
                                                Value::wrap_dict_entry(&index_val, value),
                                            );
                                            return Ok(Control::Next);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
                if let Some(obj_val) = env.get(obj_name).cloned() {
                    match obj_val {
                        Value::ClassInstance(instance) => {
                            // Mutate in place under the instance's field lock so hot
                            // raster loops (`self.buf[i] = color`) do not clone the
                            // whole container per write. Resolve the index/key BEFORE
                            // taking the field lock: index_val could reference this
                            // same instance, and re-entering its RwLock inside
                            // field_mut would deadlock.
                            let pre_idx = index_val.as_int().ok().map(|v| v as usize);
                            let pre_key = index_val.to_key_string();
                            let mutated = instance.field_mut(field_name, |slot| -> Result<(), CompileError> {
                                match slot {
                                    Value::Array(arc) => {
                                        let idx = pre_idx.ok_or_else(|| {
                                            CompileError::semantic("array index must be an integer".to_string())
                                        })?;
                                        let arr = Arc::make_mut(arc);
                                        if idx < arr.len() {
                                            arr[idx] = value.clone();
                                        } else {
                                            while arr.len() < idx {
                                                arr.push(Value::Nil);
                                            }
                                            arr.push(value.clone());
                                        }
                                        Ok(())
                                    }
                                    // A buffer handed back by a runtime allocator
                                    // (`rt_byte_array_new`, `rt_bytes_alloc`) is a
                                    // `Value::ByteArray`, not a `Value::Array`, so
                                    // without this arm `self.buf[i] = v` fell to the
                                    // catch-all and failed with "cannot index assign
                                    // to field `buf` of type array" — a message that
                                    // names the type it just refused. Every
                                    // preallocate-then-fill module was pushed onto a
                                    // dead path by that. See
                                    // doc/08_tracking/bug/interpreter_raw_array_and_glob_import_gaps_2026-08-21.md item 1.
                                    // Frozen variants are deliberately NOT accepted:
                                    // rejecting a write to a frozen buffer is correct.
                                    Value::ByteArray(arc) => {
                                        let idx = pre_idx.ok_or_else(|| {
                                            CompileError::semantic("array index must be an integer".to_string())
                                        })?;
                                        let byte = value.as_int()? as u8;
                                        let bytes = Arc::make_mut(arc);
                                        if idx < bytes.len() {
                                            bytes[idx] = byte;
                                        } else {
                                            while bytes.len() < idx {
                                                bytes.push(0);
                                            }
                                            bytes.push(byte);
                                        }
                                        Ok(())
                                    }
                                    // A fixed-size array has a declared length that an
                                    // index assignment must not change, so an
                                    // out-of-range index is an error rather than a grow.
                                    Value::FixedSizeArray { data, .. } => {
                                        let idx = pre_idx.ok_or_else(|| {
                                            CompileError::semantic("array index must be an integer".to_string())
                                        })?;
                                        if idx < data.len() {
                                            data[idx] = value.clone();
                                            Ok(())
                                        } else {
                                            let ctx = ErrorContext::new()
                                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                                .with_help(format!("array has {} element(s)", data.len()))
                                                .with_note(format!("index {} is out of bounds", idx));
                                            Err(CompileError::semantic_with_context(
                                                format!(
                                                    "index out of bounds: array index {} out of bounds (len={})",
                                                    idx,
                                                    data.len()
                                                ),
                                                ctx,
                                            ))
                                        }
                                    }
                                    Value::Dict(dict) => {
                                        let stored = Value::wrap_dict_entry(&index_val, value.clone());
                                        Arc::make_mut(dict).insert(pre_key.clone(), stored);
                                        Ok(())
                                    }
                                    Value::Tuple(tup) => {
                                        let idx = pre_idx.ok_or_else(|| {
                                            CompileError::semantic("tuple index must be an integer".to_string())
                                        })?;
                                        if idx < tup.len() {
                                            tup[idx] = value.clone();
                                            Ok(())
                                        } else {
                                            let ctx = ErrorContext::new()
                                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                                .with_help(format!("tuple has {} element(s)", tup.len()))
                                                .with_note(format!("index {} is out of bounds", idx));
                                            Err(CompileError::semantic_with_context(
                                                format!(
                                                    "index out of bounds: tuple index {} out of bounds (len={})",
                                                    idx,
                                                    tup.len()
                                                ),
                                                ctx,
                                            ))
                                        }
                                    }
                                    other => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::INVALID_ASSIGNMENT)
                                            .with_help("index assignment requires an array, dict, or tuple");
                                        Err(CompileError::semantic_with_context(
                                            format!(
                                                "invalid assignment: cannot index assign to field `{}` of type {}",
                                                field_name,
                                                other.type_name()
                                            ),
                                            ctx,
                                        ))
                                    }
                                }
                            });
                            match mutated {
                                Some(result) => {
                                    result?;
                                    Ok(Control::Next)
                                }
                                None => {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::INVALID_ASSIGNMENT)
                                        .with_help("field does not exist on this object");
                                    Err(CompileError::semantic_with_context(
                                        format!("invalid assignment: field `{}` not found on object", field_name),
                                        ctx,
                                    ))
                                }
                            }
                        }
                        Value::Object { class, fields } => {
                            let mut fields = fields;
                            if let Some(container) = fields.get(field_name).cloned() {
                                let new_container = match container {
                                    Value::Array(mut arc) => {
                                        let arr = Arc::make_mut(&mut arc);
                                        let idx = index_val.as_int()? as usize;
                                        if idx < arr.len() {
                                            arr[idx] = value;
                                        } else {
                                            while arr.len() < idx {
                                                arr.push(Value::Nil);
                                            }
                                            arr.push(value);
                                        }
                                        Value::Array(arc)
                                    }
                                    // Same runtime-allocator buffer case as the
                                    // ClassInstance path above (`rt_byte_array_new` /
                                    // `rt_bytes_alloc` hand back a `Value::ByteArray`,
                                    // not a `Value::Array`). Frozen variants stay
                                    // rejected on purpose.
                                    Value::ByteArray(mut arc) => {
                                        let idx = index_val.as_int()? as usize;
                                        let byte = value.as_int()? as u8;
                                        let bytes = Arc::make_mut(&mut arc);
                                        if idx < bytes.len() {
                                            bytes[idx] = byte;
                                        } else {
                                            while bytes.len() < idx {
                                                bytes.push(0);
                                            }
                                            bytes.push(byte);
                                        }
                                        Value::ByteArray(arc)
                                    }
                                    Value::FixedSizeArray { mut data, size } => {
                                        let idx = index_val.as_int()? as usize;
                                        if idx < data.len() {
                                            data[idx] = value;
                                            Value::FixedSizeArray { data, size }
                                        } else {
                                            let ctx = ErrorContext::new()
                                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                                .with_help(format!("array has {} element(s)", data.len()))
                                                .with_note(format!("index {} is out of bounds", idx));
                                            return Err(CompileError::semantic_with_context(
                                                format!(
                                                    "index out of bounds: array index {} out of bounds (len={})",
                                                    idx,
                                                    data.len()
                                                ),
                                                ctx,
                                            ));
                                        }
                                    }
                                    Value::Dict(mut dict) => {
                                        let key = index_val.to_key_string();
                                        let stored = Value::wrap_dict_entry(&index_val, value);
                                        Arc::make_mut(&mut dict).insert(key, stored);
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
                                                format!(
                                                    "index out of bounds: tuple index {} out of bounds (len={})",
                                                    idx,
                                                    tup.len()
                                                ),
                                                ctx,
                                            ));
                                        }
                                    }
                                    _ => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::INVALID_ASSIGNMENT)
                                            .with_help("index assignment requires an array, dict, or tuple");
                                        return Err(CompileError::semantic_with_context(
                                            format!(
                                                "invalid assignment: cannot index assign to field `{}` of type {}",
                                                field_name,
                                                container.type_name()
                                            ),
                                            ctx,
                                        ));
                                    }
                                };
                                Arc::make_mut(&mut fields).insert(field_name.clone(), new_container);
                                env.insert(obj_name.clone(), Value::Object { class, fields });
                                Ok(Control::Next)
                            } else {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::INVALID_ASSIGNMENT)
                                    .with_help("field does not exist on this object");
                                Err(CompileError::semantic_with_context(
                                    format!("invalid assignment: field `{}` not found on object", field_name),
                                    ctx,
                                ))
                            }
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_ASSIGNMENT)
                                .with_help("field assignment requires an object with mutable access");
                            Err(CompileError::semantic_with_context(
                                "invalid assignment: cannot assign field index on non-object value",
                                ctx,
                            ))
                        }
                    }
                } else {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("check that the variable is defined and in scope");
                    Err(CompileError::semantic_with_context(
                        format!("variable `{}` not found", obj_name),
                        ctx,
                    ))
                }
            } else if let Expr::FieldAccess {
                receiver: inner_obj_expr,
                field: inner_field_name,
            } = obj_expr.as_ref()
            {
                // Handle nested field access: self.ctx.dict[key] = value
                // This is obj.field1.field2[index] = value
                if let Expr::Identifier(root_name) = inner_obj_expr.as_ref() {
                    if let Some(Value::Object {
                        class: r_class,
                        fields: r_fields,
                    }) = env.get(root_name).cloned()
                    {
                        let mut root_fields = r_fields;
                        let root_class = r_class;
                        if let Some(Value::Object {
                            class: i_class,
                            fields: i_fields,
                        }) = root_fields.get(inner_field_name).cloned()
                        {
                            let mut inner_fields = i_fields;
                            let inner_class = i_class;
                            if let Some(container) = inner_fields.get(field_name).cloned() {
                                let new_container = match container {
                                    Value::Array(mut arc) => {
                                        let arr = Arc::make_mut(&mut arc);
                                        let idx = index_val.as_int()? as usize;
                                        if idx < arr.len() {
                                            arr[idx] = value;
                                        } else {
                                            while arr.len() < idx {
                                                arr.push(Value::Nil);
                                            }
                                            arr.push(value);
                                        }
                                        Value::Array(arc)
                                    }
                                    // Same runtime-allocator buffer case as the
                                    // ClassInstance path above (`rt_byte_array_new` /
                                    // `rt_bytes_alloc` hand back a `Value::ByteArray`,
                                    // not a `Value::Array`). Frozen variants stay
                                    // rejected on purpose.
                                    Value::ByteArray(mut arc) => {
                                        let idx = index_val.as_int()? as usize;
                                        let byte = value.as_int()? as u8;
                                        let bytes = Arc::make_mut(&mut arc);
                                        if idx < bytes.len() {
                                            bytes[idx] = byte;
                                        } else {
                                            while bytes.len() < idx {
                                                bytes.push(0);
                                            }
                                            bytes.push(byte);
                                        }
                                        Value::ByteArray(arc)
                                    }
                                    Value::FixedSizeArray { mut data, size } => {
                                        let idx = index_val.as_int()? as usize;
                                        if idx < data.len() {
                                            data[idx] = value;
                                            Value::FixedSizeArray { data, size }
                                        } else {
                                            let ctx = ErrorContext::new()
                                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                                .with_help(format!("array has {} element(s)", data.len()))
                                                .with_note(format!("index {} is out of bounds", idx));
                                            return Err(CompileError::semantic_with_context(
                                                format!(
                                                    "index out of bounds: array index {} out of bounds (len={})",
                                                    idx,
                                                    data.len()
                                                ),
                                                ctx,
                                            ));
                                        }
                                    }
                                    Value::Dict(mut dict) => {
                                        let key = index_val.to_key_string();
                                        let stored = Value::wrap_dict_entry(&index_val, value);
                                        Arc::make_mut(&mut dict).insert(key, stored);
                                        Value::Dict(dict)
                                    }
                                    _ => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::INVALID_ASSIGNMENT)
                                            .with_help("nested index assignment requires an array or dict");
                                        return Err(CompileError::semantic_with_context(
                                            format!(
                                                "invalid assignment: cannot index assign to field `{}` of type {}",
                                                field_name,
                                                container.type_name()
                                            ),
                                            ctx,
                                        ));
                                    }
                                };
                                Arc::make_mut(&mut inner_fields).insert(field_name.clone(), new_container);
                                let new_inner_obj = Value::Object {
                                    class: inner_class,
                                    fields: inner_fields,
                                };
                                Arc::make_mut(&mut root_fields).insert(inner_field_name.clone(), new_inner_obj);
                                env.insert(
                                    root_name.clone(),
                                    Value::Object {
                                        class: root_class,
                                        fields: root_fields,
                                    },
                                );
                                return Ok(Control::Next);
                            }
                        }
                    }
                }
                // General place fallback: an arbitrary projection chain rooted at a
                // variable (`self.a[i].b[k] = v`, `self.rows[i].cols[j] = v`).
                // `place::resolve_place` + `write_place` already walk any depth with
                // `Arc::make_mut`, so this is the same copy-on-write contract the
                // hand-written two-level cases use — a uniquely-owned container
                // mutates in place, a genuinely aliased one deep-copies first. The
                // hand-written cases above stop at `ident[i]` and `ident.field[i]`;
                // anything deeper used to be rejected outright, forcing callers into
                // a read-modify-write round trip (`var row = self.rows[i]; row.x[k]
                // = v; self.rows[i] = row`) whose intermediate binding ALIASES the
                // inner container and therefore pays a full O(n) COW clone on every
                // single write.
                // `receiver` is resolved as the place and the ALREADY-EVALUATED
                // `index_val` is appended, so no index expression is evaluated twice.
                if let Some(mut place) =
                    super::place::resolve_place(receiver, env, functions, classes, enums, impl_methods)?
                {
                    place.projections.push(super::place::Projection::Index(index_val));
                    if super::place::write_place(env, &place, value) {
                        return Ok(Control::Next);
                    }
                }
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help("nested field access index assignment requires a simple identifier chain");
                Err(CompileError::semantic_with_context(
                    "invalid assignment: nested field access not fully supported",
                    ctx,
                ))
            } else {
                // General place fallback: an arbitrary projection chain rooted at a
                // variable (`self.a[i].b[k] = v`, `self.rows[i].cols[j] = v`).
                // `place::resolve_place` + `write_place` already walk any depth with
                // `Arc::make_mut`, so this is the same copy-on-write contract the
                // hand-written two-level cases use — a uniquely-owned container
                // mutates in place, a genuinely aliased one deep-copies first. The
                // hand-written cases above stop at `ident[i]` and `ident.field[i]`;
                // anything deeper used to be rejected outright, forcing callers into
                // a read-modify-write round trip (`var row = self.rows[i]; row.x[k]
                // = v; self.rows[i] = row`) whose intermediate binding ALIASES the
                // inner container and therefore pays a full O(n) COW clone on every
                // single write.
                // `receiver` is resolved as the place and the ALREADY-EVALUATED
                // `index_val` is appended, so no index expression is evaluated twice.
                if let Some(mut place) =
                    super::place::resolve_place(receiver, env, functions, classes, enums, impl_methods)?
                {
                    place.projections.push(super::place::Projection::Index(index_val));
                    if super::place::write_place(env, &place, value) {
                        return Ok(Control::Next);
                    }
                }
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help("index assignment on field access requires an identifier as the object");
                Err(CompileError::semantic_with_context(
                    "invalid assignment: complex field access not supported",
                    ctx,
                ))
            }
        } else {
            // General place fallback: an arbitrary projection chain rooted at a
            // variable (`self.a[i].b[k] = v`, `self.rows[i].cols[j] = v`).
            // `place::resolve_place` + `write_place` already walk any depth with
            // `Arc::make_mut`, so this is the same copy-on-write contract the
            // hand-written two-level cases use — a uniquely-owned container
            // mutates in place, a genuinely aliased one deep-copies first. The
            // hand-written cases above stop at `ident[i]` and `ident.field[i]`;
            // anything deeper used to be rejected outright, forcing callers into
            // a read-modify-write round trip (`var row = self.rows[i]; row.x[k]
            // = v; self.rows[i] = row`) whose intermediate binding ALIASES the
            // inner container and therefore pays a full O(n) COW clone on every
            // single write.
            // `receiver` is resolved as the place and the ALREADY-EVALUATED
            // `index_val` is appended, so no index expression is evaluated twice.
            if let Some(mut place) =
                super::place::resolve_place(receiver, env, functions, classes, enums, impl_methods)?
            {
                place.projections.push(super::place::Projection::Index(index_val));
                if super::place::write_place(env, &place, value) {
                    return Ok(Control::Next);
                }
            }
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help("index assignment requires an identifier or field access as the container");
            Err(CompileError::semantic_with_context(
                "invalid assignment: index assignment requires identifier or field access as container",
                ctx,
            ))
        }
    } else if let Expr::Tuple(targets) = &assign.target {
        // Handle tuple unpacking: (a, b) = (x, y)
        let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        let values: Vec<Value> = match value {
            Value::Tuple(v) => v,
            Value::Array(arc) => Arc::unwrap_or_clone(arc),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("tuple unpacking requires a tuple or array on the right side");
                return Err(CompileError::semantic_with_context(
                    format!(
                        "type mismatch: tuple unpacking requires tuple or array, got {}",
                        value.type_name()
                    ),
                    ctx,
                ));
            }
        };
        if targets.len() != values.len() {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("ensure the right side has the same number of elements as the left side");
            return Err(CompileError::semantic_with_context(
                format!(
                    "argument count mismatch: tuple unpacking expected {}, got {}",
                    targets.len(),
                    values.len()
                ),
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

/// Fast-path helper: `arr = arr + [e1, e2, ...]` / `arr += [e1, e2, ...]` on a
/// `Value::Array` — push elements in place instead of allocating a fresh array
/// and copying both sides. Turns the idiomatic append loop from O(N^2) into
/// amortized O(N). Shared by both `exec_assignment` (plain assign) and
/// `exec_augmented_assignment` (AddAssign).
///
/// Returns `Ok(true)` if the fast path fired (caller is done), `Ok(false)` if
/// the shape didn't match (caller should take its normal path), or an error if
/// one of the RHS element evaluations failed.
fn try_array_append_in_place(
    name: &str,
    items: &[Expr],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<bool, CompileError> {
    // Reject array literals containing spread elements — they need the slow path.
    if items.iter().any(|e| matches!(e, Expr::Spread(_))) {
        return Ok(false);
    }
    // Only fire when the current binding is a Value::Array.
    if !matches!(env.get(name), Some(Value::Array(_))) {
        return Ok(false);
    }
    // Evaluate all RHS elements first (so any side effects run before we take
    // ownership of the LHS array).
    let mut evaluated: Vec<Value> = Vec::with_capacity(items.len());
    for item in items {
        evaluated.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
    }
    // Re-check after side effects in case RHS evaluation rebound `name`.
    if let Some(Value::Array(arc)) = env.remove(name) {
        let mut arc = arc;
        let v = Arc::make_mut(&mut arc);
        v.reserve(evaluated.len());
        for val in evaluated {
            v.push(val);
        }
        env.insert(name.to_string(), Value::Array(arc));
        return Ok(true);
    }
    Ok(false)
}

/// Fast-path helper: `s = s + rhs` / `s += rhs` on a `Value::Str` — append the
/// RHS string in place instead of allocating a fresh `String` via `format!`.
/// Turns the idiomatic `while: s += "x"` loop from O(N^2) into amortized O(N).
/// Shared by both `exec_assignment` (plain assign) and `exec_augmented_assignment`
/// (AddAssign).
///
/// `rhs` is an arbitrary expression and may have side effects — they are
/// evaluated before we take ownership of the LHS. Returns `Ok(Some(rhs_value))`
/// if the RHS did not evaluate to a `Value::Str` (caller should take its normal
/// path using the already-evaluated value), `Ok(None)` if the fast path fired
/// (caller is done), or an error if RHS evaluation failed.
fn try_string_append_in_place(
    name: &str,
    rhs: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Only fire when the current binding is a Value::Str.
    if !matches!(env.get(name), Some(Value::Str(_))) {
        return Ok(Some(evaluate_expr(rhs, env, functions, classes, enums, impl_methods)?));
    }
    // Evaluate RHS first so any side effects run before we take ownership of
    // the LHS string.
    let rhs_val = evaluate_expr(rhs, env, functions, classes, enums, impl_methods)?;
    let Value::Str(rhs_str) = rhs_val else {
        // Not a string-string concat — the generic path needs to handle the
        // non-string-plus-string cases (e.g. `s + i` → display coercion).
        return Ok(Some(rhs_val));
    };
    // Re-check after side effects in case RHS evaluation rebound `name`.
    if let Some(Value::Str(s)) = env.remove(name) {
        // `env.remove` above took the binding OUT of the environment, so when
        // this variable is the only holder the Arc strong count is now 1 and
        // `try_unwrap` hands back the owned `String` — we then `push_str` into
        // its existing buffer, which grows with `String`'s amortized doubling.
        // That is what makes a repeated `s = s + x` loop O(N) total instead of
        // O(N^2).
        //
        // Before 2026-08-21 this unconditionally did `s.as_ref().clone()`,
        // deep-copying the whole string on EVERY append, so the "fast path"
        // still allocated a fresh N-byte buffer per iteration and the loop
        // stayed quadratic — 40k appends took ~56 s and drove ~450 MB RSS to
        // build a 40 KB string, 94% of it kernel time servicing page faults for
        // buffers that could never be reused (each request was 2 bytes larger
        // than the last, defeating size-class reuse).
        // See doc/08_tracking/bug/seed_interpreter_raw_throughput_2026-08-21.md
        //
        // The aliased case is unchanged: if another holder still references the
        // string, `try_unwrap` fails and we copy exactly as before, so value
        // semantics are preserved.
        let mut result = Arc::try_unwrap(s).unwrap_or_else(|shared| shared.as_ref().clone());
        result.push_str(rhs_str.as_str());
        env.insert(name.to_string(), Value::text(result));
        Ok(None)
    } else {
        // RHS side effect rebound `name` to a non-string. Return the RHS value
        // so the caller can fall back to the generic combine path.
        Ok(Some(Value::Str(rhs_str)))
    }
}

// Helper function for augmented assignment
pub(crate) fn exec_augmented_assignment(
    assign: &simple_parser::ast::AssignmentStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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
        AssignOp::ModAssign => Some(BinOp::Mod),
        AssignOp::SuspendAssign => None, // ~= is simple await assignment
        AssignOp::Assign => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("plain assignment (=) should be handled by the standard assignment function");
            return Err(CompileError::semantic_with_context(
                "invalid operation: plain assignment should be handled elsewhere",
                ctx,
            ));
        }
    };

    // Handle identifier targets: x += 1 or x ~+= promise
    if let Expr::Identifier(name) = &assign.target {
        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            return Err(crate::error::factory::cannot_assign_to_const(name));
        }

        // Fast path: `arr += [e1, e2, ...]` on a Value::Array — push elements in place
        // instead of allocating a fresh array and copying both sides. This turns the
        // idiomatic `arr += [item]` loop from O(N^2) into amortized O(N).
        // Only the non-suspending AddAssign case qualifies: the semantics of `~+=`
        // on arrays are not defined and field/index targets are handled below.
        if matches!(assign.op, AssignOp::AddAssign) {
            let items: Option<&[Expr]> = match &assign.value {
                Expr::Array(v) | Expr::VecLiteral(v) => Some(v.as_slice()),
                _ => None,
            };
            if let Some(items) = items {
                if try_array_append_in_place(name, items, env, functions, classes, enums, impl_methods)? {
                    return Ok(Control::Next);
                }
            }
        }

        // Fast path: `s += expr` on a Value::Str — append in place (O(N)) if
        // the RHS evaluates to a Value::Str. Otherwise we get back the
        // already-evaluated RHS value so we don't double-run side effects.
        let mut pre_evaluated_rhs: Option<Value> = None;
        if matches!(assign.op, AssignOp::AddAssign) {
            match try_string_append_in_place(name, &assign.value, env, functions, classes, enums, impl_methods)? {
                None => return Ok(Control::Next),
                Some(val) => {
                    // Only stash if the LHS was a string (meaning RHS was already
                    // evaluated). If LHS wasn't a string, the helper returned the
                    // freshly evaluated RHS too, but we can't easily distinguish.
                    // Since evaluate_expr below would re-run side effects, we must
                    // always use the returned value.
                    pre_evaluated_rhs = Some(val);
                }
            }
        }

        // Evaluate the RHS (unless the string fast path already did it)
        let mut rhs_value = match pre_evaluated_rhs {
            Some(v) => v,
            None => evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?,
        };

        // If suspension, await the value
        if is_suspend {
            rhs_value = await_value(rhs_value)?;
        }

        // If compound assignment, combine with current value
        let new_value = if let Some(op) = bin_op {
            // Create a binary expression and evaluate it
            let current = env.get(name).cloned().ok_or_else(|| {
                // E1001 - Undefined Variable
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_VARIABLE)
                    .with_help("check that the variable is defined and in scope");
                CompileError::semantic_with_context(format!("variable `{}` not found", name), ctx)
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
            // Evaluate RHS while object is still in env (RHS may reference self.field)
            let mut rhs_value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
            if is_suspend {
                rhs_value = await_value(rhs_value)?;
            }
            if let Some(obj_val) = env.remove(obj_name) {
                match obj_val {
                    Value::Object { class, mut fields } => {
                        let new_value = if let Some(op) = bin_op {
                            let current = fields
                                .get(field)
                                .cloned()
                                .ok_or_else(|| crate::error::factory::undefined_field(field))?;
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

                        Arc::make_mut(&mut fields).insert(field.clone(), new_value);
                        env.insert(obj_name.clone(), Value::Object { class, fields });
                        Ok(Control::Next)
                    }
                    Value::ClassInstance(instance) => {
                        let new_value = if let Some(op) = bin_op {
                            let current = instance
                                .field(field)
                                .ok_or_else(|| crate::error::factory::undefined_field(field))?;
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
                        instance.set_field(field.clone(), new_value);
                        env.insert(obj_name.clone(), Value::ClassInstance(instance));
                        Ok(Control::Next)
                    }
                    other => {
                        env.insert(obj_name.clone(), other);
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help("augmented assignment on fields requires an object value");
                        Err(CompileError::semantic_with_context(
                            "invalid assignment: cannot use augmented assignment on non-object value",
                            ctx,
                        ))
                    }
                }
            } else {
                let global_obj = MODULE_GLOBALS.with(|cell| cell.borrow().get(obj_name).cloned());
                if let Some(obj_val) = global_obj {
                    match obj_val {
                        Value::Object { class, mut fields } => {
                            let new_value = if let Some(op) = bin_op {
                                let current = fields
                                    .get(field)
                                    .cloned()
                                    .ok_or_else(|| crate::error::factory::undefined_field(field))?;
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

                            Arc::make_mut(&mut fields).insert(field.clone(), new_value);
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut()
                                    .insert(obj_name.clone(), Value::Object { class, fields });
                            });
                            Ok(Control::Next)
                        }
                        Value::ClassInstance(instance) => {
                            let new_value = if let Some(op) = bin_op {
                                let current = instance
                                    .field(field)
                                    .ok_or_else(|| crate::error::factory::undefined_field(field))?;
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
                            instance.set_field(field.clone(), new_value);
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut()
                                    .insert(obj_name.clone(), Value::ClassInstance(instance));
                            });
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
                        }
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
            }
        }
        // Case 2: Nested field access: obj.inner.field += value
        else if let Expr::FieldAccess {
            receiver: inner_receiver,
            field: inner_field,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(obj_name) = inner_receiver.as_ref() {
                if let Some(obj_val) = env.get(obj_name).cloned() {
                    match obj_val {
                        Value::Object { class, fields } => {
                            let mut fields = fields;
                            // Get the inner object
                            if let Some(inner_val) = fields.get(inner_field).cloned() {
                                match inner_val {
                                    Value::Object {
                                        class: inner_class,
                                        fields: inner_fields,
                                    } => {
                                        let mut inner_fields = inner_fields;
                                        // Evaluate the RHS
                                        let mut rhs_value =
                                            evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;

                                        // If suspension, await the value
                                        if is_suspend {
                                            rhs_value = await_value(rhs_value)?;
                                        }

                                        // If compound assignment, combine with current value
                                        let new_value = if let Some(op) = bin_op {
                                            let current = inner_fields
                                                .get(field)
                                                .cloned()
                                                .ok_or_else(|| crate::error::factory::undefined_field(field))?;
                                            let temp_lhs = "__lhs_temp__".to_string();
                                            let temp_rhs = "__rhs_temp__".to_string();
                                            env.insert(temp_lhs.clone(), current);
                                            env.insert(temp_rhs.clone(), rhs_value);
                                            let binary_expr = Expr::Binary {
                                                op,
                                                left: Box::new(Expr::Identifier(temp_lhs.clone())),
                                                right: Box::new(Expr::Identifier(temp_rhs.clone())),
                                            };
                                            let result = evaluate_expr(
                                                &binary_expr,
                                                env,
                                                functions,
                                                classes,
                                                enums,
                                                impl_methods,
                                            )?;
                                            env.remove(&temp_lhs);
                                            env.remove(&temp_rhs);
                                            result
                                        } else {
                                            rhs_value
                                        };

                                        // Set the field on the inner object
                                        Arc::make_mut(&mut inner_fields).insert(field.clone(), new_value);
                                        // Update the inner object in the outer object
                                        Arc::make_mut(&mut fields).insert(
                                            inner_field.clone(),
                                            Value::Object {
                                                class: inner_class,
                                                fields: inner_fields,
                                            },
                                        );
                                        // Update the outer object in env
                                        env.insert(obj_name.clone(), Value::Object { class, fields });
                                        Ok(Control::Next)
                                    }
                                    _ => {
                                        let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                                            "nested augmented field assignment requires inner value to be an object",
                                        );
                                        Err(CompileError::semantic_with_context(
                                            format!(
                                                "invalid assignment: cannot use augmented assignment on field '{}' of non-object field '{}'",
                                                field, inner_field
                                            ),
                                            ctx,
                                        ))
                                    }
                                }
                            } else {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("check the field name");
                                Err(CompileError::semantic_with_context(
                                    format!("field '{}' not found on object", inner_field),
                                    ctx,
                                ))
                            }
                        }
                        Value::ClassInstance(instance) => {
                            let inner_val = instance.field(inner_field);
                            let mut rhs_value =
                                evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                            if is_suspend {
                                rhs_value = await_value(rhs_value)?;
                            }
                            match inner_val {
                                Some(Value::ClassInstance(inner_inst)) => {
                                    let current = inner_inst
                                        .field(field)
                                        .ok_or_else(|| crate::error::factory::undefined_field(field))?;
                                    let new_value = if let Some(op) = bin_op {
                                        let temp_lhs = "__lhs_temp__".to_string();
                                        let temp_rhs = "__rhs_temp__".to_string();
                                        env.insert(temp_lhs.clone(), current);
                                        env.insert(temp_rhs.clone(), rhs_value);
                                        let binary_expr = Expr::Binary {
                                            op,
                                            left: Box::new(Expr::Identifier(temp_lhs.clone())),
                                            right: Box::new(Expr::Identifier(temp_rhs.clone())),
                                        };
                                        let result =
                                            evaluate_expr(&binary_expr, env, functions, classes, enums, impl_methods)?;
                                        env.remove(&temp_lhs);
                                        env.remove(&temp_rhs);
                                        result
                                    } else {
                                        rhs_value
                                    };
                                    inner_inst.set_field(field.clone(), new_value);
                                    Ok(Control::Next)
                                }
                                Some(Value::Object {
                                    class: inner_class,
                                    fields: inner_fields,
                                }) => {
                                    let mut inner_fields = inner_fields;
                                    let current = inner_fields
                                        .get(field)
                                        .cloned()
                                        .ok_or_else(|| crate::error::factory::undefined_field(field))?;
                                    let new_value = if let Some(op) = bin_op {
                                        let temp_lhs = "__lhs_temp__".to_string();
                                        let temp_rhs = "__rhs_temp__".to_string();
                                        env.insert(temp_lhs.clone(), current);
                                        env.insert(temp_rhs.clone(), rhs_value);
                                        let binary_expr = Expr::Binary {
                                            op,
                                            left: Box::new(Expr::Identifier(temp_lhs.clone())),
                                            right: Box::new(Expr::Identifier(temp_rhs.clone())),
                                        };
                                        let result =
                                            evaluate_expr(&binary_expr, env, functions, classes, enums, impl_methods)?;
                                        env.remove(&temp_lhs);
                                        env.remove(&temp_rhs);
                                        result
                                    } else {
                                        rhs_value
                                    };
                                    Arc::make_mut(&mut inner_fields).insert(field.clone(), new_value);
                                    instance.set_field(
                                        inner_field.clone(),
                                        Value::Object {
                                            class: inner_class,
                                            fields: inner_fields,
                                        },
                                    );
                                    Ok(Control::Next)
                                }
                                Some(_) => {
                                    let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                                        "nested augmented field assignment requires inner value to be an object",
                                    );
                                    Err(CompileError::semantic_with_context(
                                        format!(
                                            "invalid assignment: cannot use augmented assignment on field '{}' of non-object field '{}'",
                                            field, inner_field
                                        ),
                                        ctx,
                                    ))
                                }
                                None => {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::UNDEFINED_FIELD)
                                        .with_help("check the field name");
                                    Err(CompileError::semantic_with_context(
                                        format!("field '{}' not found on object", inner_field),
                                        ctx,
                                    ))
                                }
                            }
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_ASSIGNMENT)
                                .with_help("nested augmented field assignment requires an object");
                            Err(CompileError::semantic_with_context(
                                "invalid assignment: cannot use augmented assignment on non-object value",
                                ctx,
                            ))
                        }
                    }
                } else {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("check that the variable is defined and in scope");
                    Err(CompileError::semantic_with_context(
                        format!("variable '{}' not found", obj_name),
                        ctx,
                    ))
                }
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_ASSIGNMENT)
                    .with_help("deeply nested augmented field assignment (more than 2 levels) is not supported");
                Err(CompileError::semantic_with_context(
                    "invalid assignment: deeply nested augmented field access requires intermediate variables",
                    ctx,
                ))
            }
        } else {
            let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                "augmented field assignment requires an identifier or simple nested field access as the object",
            );
            Err(CompileError::semantic_with_context(
                "invalid assignment: augmented field assignment requires identifier or simple nested field access as object",
                ctx,
            ))
        }
    }
    // Handle indexed targets: arr[i] += 1, dict[k] += 1, obj.field[i] += 1
    //
    // Bug: doc/08_tracking/bug/spec_runner_indexed_augmented_assignment_unsupported_2026-08-15.md
    // Previously this fell through to the catch-all below and reported
    // "unsupported augmented assignment target" for every indexed lvalue.
    //
    // Strategy: desugar `recv[idx] op= rhs` into a PLAIN assignment
    // `recv[__idx_temp__] = recv[__idx_temp__] op __rhs_temp__` and delegate to
    // `exec_assignment`, which already owns the full indexed-store path
    // (arrays, dicts, nested field receivers, writeback). The index expression
    // is evaluated exactly ONCE into a temp binding so that side-effecting
    // subscripts (`arr[next()] += 1`) do not run twice.
    else if let Expr::Index { receiver, index } = &assign.target {
        let idx_value = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
        let idx_temp = "__aug_idx_temp__".to_string();
        let rhs_temp = "__aug_rhs_temp__".to_string();

        let mut rhs_value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
        if is_suspend {
            rhs_value = await_value(rhs_value)?;
        }

        // Save/restore any shadowed bindings so the temps never leak.
        let saved_idx = env.get(&idx_temp).cloned();
        let saved_rhs = env.get(&rhs_temp).cloned();
        env.insert(idx_temp.clone(), idx_value);
        env.insert(rhs_temp.clone(), rhs_value);

        let stable_target = Expr::Index {
            receiver: receiver.clone(),
            index: Box::new(Expr::Identifier(idx_temp.clone())),
        };
        let value_expr = match bin_op {
            Some(op) => Expr::Binary {
                op,
                left: Box::new(stable_target.clone()),
                right: Box::new(Expr::Identifier(rhs_temp.clone())),
            },
            // `~=` is a plain (awaited) assignment.
            None => Expr::Identifier(rhs_temp.clone()),
        };
        let plain = simple_parser::ast::AssignmentStmt {
            span: assign.span,
            target: stable_target,
            op: AssignOp::Assign,
            value: value_expr,
        };
        let result = exec_assignment(&plain, env, functions, classes, enums, impl_methods);

        match saved_idx {
            Some(v) => env.insert(idx_temp, v),
            None => env.remove(&idx_temp),
        };
        match saved_rhs {
            Some(v) => env.insert(rhs_temp, v),
            None => env.remove(&rhs_temp),
        };
        result
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

#[cfg(test)]
mod struct_local_alias_cow_tests {
    use super::*;
    use simple_parser::Span;

    /// Bug #187 (reported): "var b = a; b.x = 41" was claimed to leak the
    /// mutation into `a` under the interpreter, mirroring the native MIR
    /// pointer-aliasing bug fixed in `ad31f0554cd` ("fix(mir): copy struct
    /// value on local-alias bind instead of aliasing"). That native bug is
    /// specific to the pointer-represented struct model on the native/LLVM
    /// path — the interpreter's `Value::Object { fields: Arc<HashMap<..>>, .. }`
    /// representation is a different animal. Field assignment (the
    /// `Value::Object` arm of `exec_assignment` above) already does
    /// `Arc::make_mut(&mut fields)` before mutating, which clones the field
    /// map whenever it is shared (Arc strong_count > 1, e.g. right after
    /// `var b = a`). This gives struct local-aliases correct copy-on-write
    /// value semantics with NO explicit bind-time copy needed — confirmed by
    /// manual repro (direct field assign, nested struct field, array-element
    /// alias, param-then-local-alias, and reverse-order mutation) all showing
    /// no leak. This test locks that guarantee in: aliasing a struct to a
    /// second local name and mutating through the alias must not be visible
    /// through the original name (and vice versa).
    #[test]
    fn field_assignment_cow_protects_struct_local_alias() {
        let mut fields = HashMap::new();
        fields.insert("x".to_string(), Value::Int(10));
        let a_value = Value::Object {
            class: "Point".to_string(),
            fields: Arc::new(fields),
        };

        let mut env = Env::new();
        env.insert("a".to_string(), a_value.clone());
        // `var b = a` — a cheap Arc-clone of the SAME underlying field map
        // (strong_count now 2), exactly like the interpreter's `Node::Let`
        // binding (`bind_pattern_value`, which does not deep-copy Object values).
        env.insert("b".to_string(), a_value);

        // b.x = 41
        let span = Span::new(0, 0, 0, 0);
        let assign = simple_parser::ast::AssignmentStmt {
            span,
            target: Expr::FieldAccess {
                receiver: Box::new(Expr::Identifier("b".to_string())),
                field: "x".to_string(),
            },
            op: AssignOp::Assign,
            value: Expr::Integer(41),
        };
        exec_assignment(
            &assign,
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("exec_assignment");

        let a_x = match env.get("a").expect("a") {
            Value::Object { fields, .. } => fields.get("x").expect("a.x").as_int().expect("int"),
            other => panic!("a must remain an Object, got {:?}", other),
        };
        let b_x = match env.get("b").expect("b") {
            Value::Object { fields, .. } => fields.get("x").expect("b.x").as_int().expect("int"),
            other => panic!("b must remain an Object, got {:?}", other),
        };
        assert_eq!(a_x, 10, "a must be unaffected by mutation through alias b");
        assert_eq!(b_x, 41, "b must observe its own mutation");
    }
}

#[cfg(test)]
mod indexed_augmented_assignment_tests {
    use super::*;
    use simple_parser::Span;

    /// Regression: `exec_augmented_assignment` had arms only for
    /// `Expr::Identifier` and `Expr::FieldAccess`, so EVERY indexed lvalue
    /// (`arr[i] += 1`, `dict[k] *= 2`, `obj.slots[i] -= 1`) hit the catch-all
    /// and raised "invalid assignment: unsupported augmented assignment
    /// target".
    /// Bug: doc/08_tracking/bug/spec_runner_indexed_augmented_assignment_unsupported_2026-08-15.md
    /// Spec: test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl
    fn run_indexed_aug(target_receiver: &str, index: Expr, op: AssignOp, rhs: i64, env: &mut Env) {
        let assign = simple_parser::ast::AssignmentStmt {
            span: Span::new(0, 0, 0, 0),
            target: Expr::Index {
                receiver: Box::new(Expr::Identifier(target_receiver.to_string())),
                index: Box::new(index),
            },
            op,
            value: Expr::Integer(rhs),
        };
        exec_augmented_assignment(
            &assign,
            env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("indexed augmented assignment must be supported");
    }

    fn elem(env: &Env, name: &str, i: usize) -> i64 {
        match env.get(name).expect("array binding") {
            Value::Array(items) => items[i].as_int().expect("int element"),
            other => panic!("expected an array, got {:?}", other),
        }
    }

    #[test]
    fn every_augmented_operator_applies_to_an_array_element() {
        let mut env = Env::new();
        env.insert(
            "xs".to_string(),
            Value::Array(Arc::new(vec![
                Value::Int(10),
                Value::Int(20),
                Value::Int(30),
                Value::Int(40),
                Value::Int(50),
            ])),
        );

        run_indexed_aug("xs", Expr::Integer(0), AssignOp::AddAssign, 5, &mut env);
        run_indexed_aug("xs", Expr::Integer(1), AssignOp::SubAssign, 5, &mut env);
        run_indexed_aug("xs", Expr::Integer(2), AssignOp::MulAssign, 2, &mut env);
        run_indexed_aug("xs", Expr::Integer(3), AssignOp::DivAssign, 4, &mut env);
        run_indexed_aug("xs", Expr::Integer(4), AssignOp::ModAssign, 7, &mut env);

        assert_eq!(elem(&env, "xs", 0), 15);
        assert_eq!(elem(&env, "xs", 1), 15);
        assert_eq!(elem(&env, "xs", 2), 60);
        assert_eq!(elem(&env, "xs", 3), 10);
        assert_eq!(elem(&env, "xs", 4), 1);
    }

    #[test]
    fn the_index_expression_is_evaluated_through_a_temp_and_left_unbound() {
        let mut env = Env::new();
        env.insert(
            "xs".to_string(),
            Value::Array(Arc::new(vec![Value::Int(1), Value::Int(2)])),
        );
        // A non-literal subscript: the desugaring must bind it to a temp,
        // then restore the environment so no `__aug_*_temp__` name leaks.
        env.insert("i".to_string(), Value::Int(1));
        run_indexed_aug(
            "xs",
            Expr::Identifier("i".to_string()),
            AssignOp::AddAssign,
            40,
            &mut env,
        );
        assert_eq!(elem(&env, "xs", 1), 42);
        assert_eq!(elem(&env, "xs", 0), 1, "other elements untouched");
        assert!(
            env.get("__aug_idx_temp__").is_none(),
            "index temp must not leak into the environment"
        );
        assert!(
            env.get("__aug_rhs_temp__").is_none(),
            "rhs temp must not leak into the environment"
        );
        assert_eq!(
            env.get("i").expect("i").as_int().expect("int"),
            1,
            "the subscript variable must be unchanged"
        );
    }
}

/// Mechanism test for the `s = s + x` in-place append fast path.
///
/// Pins the fix in `try_string_append_in_place`: `env.remove(name)` drops the
/// environment's reference so `Arc::try_unwrap` yields the owned `String`, and
/// `push_str` then grows that buffer in place with `String`'s amortized
/// doubling. The observable consequence is that the string's DATA POINTER
/// changes only O(log N) times across N appends (once per capacity doubling)
/// instead of every single append.
///
/// Before the fix the body did `s.as_ref().clone()` unconditionally, so every
/// append allocated a fresh exact-sized buffer and copied the whole string:
/// N distinct buffers, O(N^2) bytes copied. A repeated-append loop grew
/// superlinearly (measured on the interpreter lane: 40k appends 0.28s -> 0.16s,
/// 80k appends 0.96s -> 0.29s, i.e. quadratic 3.4x-per-doubling -> linear 1.8x).
///
/// This assertion is deterministic — it counts allocations, not time — so it is
/// stable on a loaded box.
/// See doc/08_tracking/bug/seed_interpreter_raw_throughput_2026-08-21.md
#[cfg(test)]
mod string_append_in_place_tests {
    use super::*;
    use simple_parser::Span;
    use std::collections::HashSet;

    fn append_loop_distinct_buffers(iterations: usize) -> (usize, String) {
        let mut env = Env::new();
        env.insert("s".to_string(), Value::text(String::new()));

        let span = Span::new(0, 0, 0, 0);
        // `s = s + "ab"`
        let assign = simple_parser::ast::AssignmentStmt {
            span,
            target: Expr::Identifier("s".to_string()),
            op: AssignOp::Assign,
            value: Expr::Binary {
                op: BinOp::Add,
                left: Box::new(Expr::Identifier("s".to_string())),
                right: Box::new(Expr::String("ab".to_string())),
            },
        };

        let mut seen: HashSet<usize> = HashSet::new();
        for _ in 0..iterations {
            exec_assignment(
                &assign,
                &mut env,
                &mut HashMap::new(),
                &mut HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            )
            .expect("exec_assignment");
            match env.get("s").expect("s must stay bound") {
                Value::Str(s) => {
                    seen.insert(s.as_str().as_ptr() as usize);
                }
                other => panic!("s must remain a Str, got {:?}", other),
            }
        }

        let final_text = match env.get("s").expect("s") {
            Value::Str(s) => s.as_ref().clone(),
            other => panic!("s must remain a Str, got {:?}", other),
        };
        (seen.len(), final_text)
    }

    #[test]
    fn repeated_append_reuses_its_buffer_instead_of_reallocating_each_time() {
        const N: usize = 20_000;
        let (distinct_buffers, text) = append_loop_distinct_buffers(N);

        // Correctness first: the fast path must still produce the right string.
        assert_eq!(text.len(), N * 2, "every append must land");
        assert!(text.starts_with("abab"), "content must be the appended text");
        assert!(text.ends_with("abab"), "content must be the appended text");

        // Mechanism: amortized doubling touches O(log N) buffers. Pre-fix this
        // was ~N (a fresh exact-sized allocation per append). The bound is set
        // far above log2(40_000) ~ 16 so incidental allocator address reuse or
        // a different growth factor cannot make it flaky, while still being
        // ~20x below the pre-fix value.
        assert!(
            distinct_buffers < 1_000,
            "expected O(log N) buffer reallocations for {N} appends (amortized \
             in-place growth), got {distinct_buffers}; a value near {N} means \
             try_string_append_in_place is deep-copying on every append again"
        );
    }

    #[test]
    fn aliased_string_is_not_mutated_in_place() {
        // Value semantics must survive the optimization: when another binding
        // still holds the same Arc, `try_unwrap` must fail and fall back to a
        // copy, leaving the alias untouched.
        let mut env = Env::new();
        env.insert("s".to_string(), Value::text("start".to_string()));
        let aliased = env.get("s").expect("s").clone();
        env.insert("alias".to_string(), aliased);

        let span = Span::new(0, 0, 0, 0);
        let assign = simple_parser::ast::AssignmentStmt {
            span,
            target: Expr::Identifier("s".to_string()),
            op: AssignOp::Assign,
            value: Expr::Binary {
                op: BinOp::Add,
                left: Box::new(Expr::Identifier("s".to_string())),
                right: Box::new(Expr::String("-more".to_string())),
            },
        };
        exec_assignment(
            &assign,
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("exec_assignment");

        match env.get("alias").expect("alias") {
            Value::Str(s) => assert_eq!(s.as_str(), "start", "alias must be unaffected"),
            other => panic!("alias must remain a Str, got {:?}", other),
        }
        match env.get("s").expect("s") {
            Value::Str(s) => assert_eq!(s.as_str(), "start-more", "s must observe its own append"),
            other => panic!("s must remain a Str, got {:?}", other),
        }
    }
}

/// Nested assignment targets: `self.a[i].b[k] = v` and friends.
///
/// The index-assignment path hand-wrote exactly two shapes (`ident[i] = v` and
/// `ident.field[i] = v`) and rejected anything deeper with
/// `invalid assignment: complex field access not supported`. That is a
/// grammar-shaped hole with a real performance cost, not just an ergonomic one:
/// the workaround it forces is a read-modify-write round trip
/// (`var row = self.rows[i]; row.cols[k] = v; self.rows[i] = row`) whose
/// intermediate binding ALIASES the inner container, so the first write to it
/// deep-copies the whole container — O(n) per outer operation, O(n^2) overall.
/// `SymbolTable.define` in the self-hosted compiler pays exactly this.
///
/// The fix routes the rejected shapes through `place::resolve_place` +
/// `write_place`, which already walk an arbitrary projection chain with
/// `Arc::make_mut`. Semantics are unchanged: a uniquely-owned container mutates
/// in place, a genuinely aliased one still copies first.
#[cfg(test)]
mod nested_assignment_target_tests {
    use super::*;
    use simple_parser::Span;

    fn obj(class: &str, fields: Vec<(&str, Value)>) -> Value {
        let mut map: HashMap<String, Value> = HashMap::new();
        for (k, v) in fields {
            map.insert(k.to_string(), v);
        }
        Value::Object {
            class: class.to_string(),
            fields: Arc::new(map),
        }
    }

    fn assign(target: Expr, value: Expr) -> simple_parser::ast::AssignmentStmt {
        simple_parser::ast::AssignmentStmt {
            span: Span::new(0, 0, 0, 0),
            target,
            op: AssignOp::Assign,
            value,
        }
    }

    fn exec(stmt: &simple_parser::ast::AssignmentStmt, env: &mut Env) -> Result<Control, CompileError> {
        exec_assignment(
            stmt,
            env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
    }

    fn ident(name: &str) -> Expr {
        Expr::Identifier(name.to_string())
    }

    fn field(recv: Expr, name: &str) -> Expr {
        Expr::FieldAccess {
            receiver: Box::new(recv),
            field: name.to_string(),
        }
    }

    fn index(recv: Expr, i: Expr) -> Expr {
        Expr::Index {
            receiver: Box::new(recv),
            index: Box::new(i),
        }
    }

    fn read(env: &Env, root: &str, path: &[&str]) -> Value {
        let mut cur = env.get(root).expect("root").clone();
        for step in path {
            cur = match (&cur, step.parse::<usize>()) {
                (Value::Array(items), Ok(i)) => items[i].clone(),
                (Value::Object { fields, .. }, _) => fields.get(*step).expect("field").clone(),
                (Value::Dict(entries), _) => entries.get(*step).expect("key").clone(),
                (other, _) => panic!("cannot project {step} out of {:?}", other),
            };
        }
        cur
    }

    /// `s.rows[0].cols[1] = 42` — three projections deep, array of structs of
    /// arrays. Rejected outright before this change.
    #[test]
    fn three_deep_field_index_field_index_assignment_lands() {
        let mut env = Env::new();
        let row = obj("Row", vec![("cols", Value::array(vec![Value::Int(0), Value::Int(0)]))]);
        env.insert("s".to_string(), obj("S", vec![("rows", Value::array(vec![row]))]));
        let target = index(field(index(field(ident("s"), "rows"), Expr::Integer(0)), "cols"), Expr::Integer(1));
        exec(&assign(target, Expr::Integer(42)), &mut env).expect("nested assignment must be accepted");
        assert_eq!(read(&env, "s", &["rows", "0", "cols", "1"]), Value::Int(42));
        assert_eq!(
            read(&env, "s", &["rows", "0", "cols", "0"]),
            Value::Int(0),
            "the sibling element must be untouched"
        );
    }

    /// `s.scopes[0].symbols["k"] = 7` — the exact SymbolTable.define shape:
    /// array of structs holding a dict.
    #[test]
    fn nested_dict_under_indexed_struct_assignment_lands() {
        let mut env = Env::new();
        let scope = obj("Scope", vec![("symbols", Value::Dict(Arc::new(HashMap::new())))]);
        env.insert("s".to_string(), obj("S", vec![("scopes", Value::array(vec![scope]))]));
        let target = index(
            field(index(field(ident("s"), "scopes"), Expr::Integer(0)), "symbols"),
            Expr::String("k".to_string()),
        );
        exec(&assign(target, Expr::Integer(7)), &mut env).expect("nested dict assignment must be accepted");
        assert_eq!(read(&env, "s", &["scopes", "0", "symbols", "k"]), Value::Int(7));
    }

    /// `grid[0][1] = 5` — index-of-index, no fields at all.
    #[test]
    fn two_deep_index_of_index_assignment_lands() {
        let mut env = Env::new();
        env.insert(
            "grid".to_string(),
            Value::array(vec![Value::array(vec![Value::Int(0), Value::Int(0)])]),
        );
        let target = index(index(ident("grid"), Expr::Integer(0)), Expr::Integer(1));
        exec(&assign(target, Expr::Integer(5)), &mut env).expect("index-of-index assignment must be accepted");
        assert_eq!(read(&env, "grid", &["0", "1"]), Value::Int(5));
    }

    /// Value semantics: a live alias of an INTERMEDIATE container must still
    /// copy-on-write and must not observe the nested write.
    #[test]
    fn live_alias_of_an_intermediate_still_copies_on_write() {
        let mut env = Env::new();
        let row = obj("Row", vec![("cols", Value::array(vec![Value::Int(0), Value::Int(0)]))]);
        env.insert("s".to_string(), obj("S", vec![("rows", Value::array(vec![row]))]));
        // `alias` holds the same rows array Arc as `s.rows`.
        let alias = read(&env, "s", &["rows"]);
        env.insert("alias".to_string(), alias);

        let target = index(field(index(field(ident("s"), "rows"), Expr::Integer(0)), "cols"), Expr::Integer(1));
        exec(&assign(target, Expr::Integer(42)), &mut env).expect("nested assignment must be accepted");

        assert_eq!(read(&env, "s", &["rows", "0", "cols", "1"]), Value::Int(42));
        assert_eq!(
            read(&env, "alias", &["0", "cols", "1"]),
            Value::Int(0),
            "the aliased intermediate must not observe the write — value semantics"
        );
    }

    /// A genuine non-place target must still be rejected, not silently dropped.
    #[test]
    fn non_place_index_target_is_still_rejected() {
        let mut env = Env::new();
        let target = index(
            Expr::MethodCall {
                receiver: Box::new(ident("nothing")),
                method: "f".to_string(),
                args: vec![],
                generic_args: vec![],
            },
            Expr::Integer(0),
        );
        let err = exec(&assign(target, Expr::Integer(1)), &mut env);
        assert!(err.is_err(), "a call-result index target is not a place and must be an error");
    }
}
