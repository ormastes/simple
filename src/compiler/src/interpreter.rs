//! Tree-walking interpreter for the Simple language.
//!
//! This module provides runtime interpretation of AST nodes, including:
//! - Expression evaluation
//! - Statement execution
//! - Control flow handling
//! - Built-in methods for arrays, dicts, strings, etc.
//! - User-defined function and lambda execution
//! - Actor/future/generator support

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, mpsc};

use simple_parser::ast::{
    AssignOp, BinOp, Block, ClassDef, ContextStmt, Effect, Expr, ExternDef, FStringPart,
    FunctionDef, IfStmt, LambdaParam, MacroArg, MacroBody, MacroDef, MacroParam, MatchStmt,
    Node, Pattern, PointerKind, RangeBound, Type, UnaryOp,
};
use simple_common::actor::{ActorSpawner, Message, ThreadSpawner};
use tracing::instrument;

use crate::effects::{check_waitless_violation, CURRENT_EFFECT};
use crate::error::CompileError;
use crate::value::{
    BorrowMutValue, BorrowValue, Env, FutureValue, GeneratorValue, ManualHandleValue,
    ManualSharedValue, ManualUniqueValue, ManualWeakValue, Value,
    BUILTIN_RANGE, BUILTIN_ARRAY,
};

// Thread-local state for interpreter execution
thread_local! {
    pub(crate) static ACTOR_SPAWNER: ThreadSpawner = ThreadSpawner::new();
    pub(crate) static ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = RefCell::new(None);
    pub(crate) static ACTOR_OUTBOX: RefCell<Option<mpsc::Sender<Message>>> = RefCell::new(None);
    pub(crate) static CONST_NAMES: RefCell<std::collections::HashSet<String>> = RefCell::new(std::collections::HashSet::new());
    pub(crate) static EXTERN_FUNCTIONS: RefCell<std::collections::HashSet<String>> = RefCell::new(std::collections::HashSet::new());
    /// Current context object for context blocks (DSL support)
    pub(crate) static CONTEXT_OBJECT: RefCell<Option<Value>> = RefCell::new(None);
    /// Accumulated yield values during generator execution
    pub(crate) static GENERATOR_YIELDS: RefCell<Option<Vec<Value>>> = RefCell::new(None);
    /// User-defined macros
    pub(crate) static USER_MACROS: RefCell<HashMap<String, MacroDef>> = RefCell::new(HashMap::new());
}

/// Stores enum definition: name -> list of variant names
pub(crate) type Enums = HashMap<String, Vec<String>>;

/// Stores impl block methods: type_name -> list of methods
pub(crate) type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Stores extern function declarations: name -> definition
pub(crate) type ExternFunctions = HashMap<String, ExternDef>;

/// Stores macro definitions: name -> definition
pub(crate) type Macros = HashMap<String, MacroDef>;

/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(Value),
    Break(Option<Value>),
    Continue,
}

/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    // Clear const names and extern functions from previous runs
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().clear());

    let mut env = Env::new();
    let mut functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut classes: HashMap<String, ClassDef> = HashMap::new();
    let mut enums: Enums = HashMap::new();
    let mut impl_methods: ImplMethods = HashMap::new();
    let mut extern_functions: ExternFunctions = HashMap::new();
    let mut macros: Macros = HashMap::new();

    for item in items {
        match item {
            Node::Function(f) => {
                functions.insert(f.name.clone(), f.clone());
            }
            Node::Struct(s) => {
                env.insert(
                    s.name.clone(),
                    Value::Object {
                        class: s.name.clone(),
                        fields: HashMap::new(),
                    },
                );
            }
            Node::Enum(e) => {
                let variants: Vec<String> = e.variants.iter().map(|v| v.name.clone()).collect();
                enums.insert(e.name.clone(), variants);
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                env.insert(
                    c.name.clone(),
                    Value::Object {
                        class: c.name.clone(),
                        fields: HashMap::new(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                let type_name = get_type_name(&impl_block.target_type);
                let methods = impl_methods.entry(type_name).or_insert_with(Vec::new);
                for method in &impl_block.methods {
                    methods.push(method.clone());
                }
            }
            Node::Extern(ext) => {
                extern_functions.insert(ext.name.clone(), ext.clone());
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::Macro(m) => {
                macros.insert(m.name.clone(), m.clone());
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
            }
            Node::Trait(t) => {
                // Register trait - currently traits are checked at type-check time
                // Store trait name for later use in impl checking
                env.insert(t.name.clone(), Value::Nil);
            }
            Node::Actor(a) => {
                // Register actor as a class-like type for instantiation
                // Actors have fields (state) and methods like classes
                classes.insert(a.name.clone(), ClassDef {
                    span: a.span,
                    name: a.name.clone(),
                    generic_params: Vec::new(),
                    fields: a.fields.clone(),
                    methods: a.methods.clone(),
                    parent: None,
                    visibility: a.visibility,
                });
                env.insert(a.name.clone(), Value::Object {
                    class: a.name.clone(),
                    fields: HashMap::new(),
                });
            }
            Node::TypeAlias(t) => {
                // Type aliases are handled at type-check time
                // Store the alias name for reference
                env.insert(t.name.clone(), Value::Nil);
            }
            Node::Let(_) | Node::Const(_) | Node::Static(_) | Node::Assignment(_) | Node::If(_) | Node::For(_) | Node::While(_) | Node::Loop(_) | Node::Match(_) | Node::Context(_) => {
                if let Control::Return(val) = exec_node(item, &mut env, &functions, &classes, &enums, &impl_methods)? {
                    return val.as_int().map(|v| v as i32);
                }
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let val = evaluate_expr(expr, &env, &functions, &classes, &enums, &impl_methods)?;
                    return val.as_int().map(|v| v as i32);
                }
                return Ok(0);
            }
            Node::Expression(expr) => {
                if let Expr::FunctionalUpdate { target, method, args } = expr {
                    if let Expr::Identifier(name) = target.as_ref() {
                        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                        if is_const {
                            return Err(CompileError::Semantic(format!("cannot use functional update on const '{name}'")));
                        }
                        let recv_val = env.get(name).cloned().ok_or_else(|| {
                            CompileError::Semantic(format!("undefined variable: {name}"))
                        })?;
                        let method_call = Expr::MethodCall {
                            receiver: Box::new(Expr::Identifier(name.clone())),
                            method: method.clone(),
                            args: args.clone(),
                        };
                        let result = evaluate_expr(&method_call, &env, &functions, &classes, &enums, &impl_methods)?;
                        let new_value = match (&recv_val, &result) {
                            (Value::Array(_), Value::Array(_)) => result,
                            (Value::Dict(_), Value::Dict(_)) => result,
                            (Value::Str(_), Value::Str(_)) => result,
                            (Value::Tuple(_), Value::Tuple(_)) => result,
                            (Value::Object { .. }, Value::Object { .. }) => result,
                            _ => env.get(name).cloned().unwrap_or(recv_val),
                        };
                        env.insert(name.clone(), new_value);
                        continue;
                    }
                    return Err(CompileError::Semantic("functional update target must be an identifier".into()));
                }
                let _ = evaluate_expr(expr, &env, &functions, &classes, &enums, &impl_methods)?;
            }
            Node::Break(_) => {
                return Err(CompileError::Semantic("break outside of loop".into()));
            }
            Node::Continue(_) => {
                return Err(CompileError::Semantic("continue outside of loop".into()));
            }
        }
    }

    let main_val = env
        .get("main")
        .cloned()
        .unwrap_or(Value::Int(0))
        .as_int()? as i32;
    Ok(main_val)
}

/// Extract type name from a Type AST node
fn get_type_name(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        _ => "unknown".to_string(),
    }
}

pub(crate) fn exec_node(
    node: &Node,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    match node {
        Node::Let(let_stmt) => {
            if let Some(value_expr) = &let_stmt.value {
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                if let Pattern::Identifier(name) = &let_stmt.pattern {
                    env.insert(name.clone(), value);
                    if !let_stmt.mutability.is_mutable() {
                        CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                    }
                } else if let Pattern::MutIdentifier(name) = &let_stmt.pattern {
                    env.insert(name.clone(), value);
                } else if let Pattern::Tuple(patterns) = &let_stmt.pattern {
                    if let Value::Tuple(values) = value {
                        for (pat, val) in patterns.iter().zip(values.into_iter()) {
                            if let Pattern::Identifier(name) = pat {
                                env.insert(name.clone(), val);
                                if !let_stmt.mutability.is_mutable() {
                                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                                }
                            } else if let Pattern::MutIdentifier(name) = pat {
                                env.insert(name.clone(), val);
                            }
                        }
                    }
                } else if let Pattern::Array(patterns) = &let_stmt.pattern {
                    if let Value::Array(values) = value {
                        for (pat, val) in patterns.iter().zip(values.into_iter()) {
                            if let Pattern::Identifier(name) = pat {
                                env.insert(name.clone(), val);
                                if !let_stmt.mutability.is_mutable() {
                                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                                }
                            } else if let Pattern::MutIdentifier(name) = pat {
                                env.insert(name.clone(), val);
                            }
                        }
                    }
                }
            }
            Ok(Control::Next)
        }
        Node::Const(const_stmt) => {
            let value = evaluate_expr(&const_stmt.value, env, functions, classes, enums, impl_methods)?;
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
            if let Expr::Identifier(name) = &assign.target {
                let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                if is_const {
                    return Err(CompileError::Semantic(format!("cannot assign to const '{name}'")));
                }
                let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                env.insert(name.clone(), value);
                Ok(Control::Next)
            } else {
                Err(CompileError::Semantic("unsupported assignment target".into()))
            }
        }
        Node::If(if_stmt) => exec_if(if_stmt, env, functions, classes, enums, impl_methods),
        Node::While(while_stmt) => exec_while(while_stmt, env, functions, classes, enums, impl_methods),
        Node::Loop(loop_stmt) => exec_loop(loop_stmt, env, functions, classes, enums, impl_methods),
        Node::For(for_stmt) => exec_for(for_stmt, env, functions, classes, enums, impl_methods),
        Node::Return(ret) => {
            let value = if let Some(expr) = &ret.value {
                evaluate_expr(expr, env, functions, classes, enums, impl_methods)?
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
        Node::Expression(expr) => {
            if let Expr::FunctionalUpdate { target, method, args } = expr {
                if let Expr::Identifier(name) = target.as_ref() {
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                    if is_const {
                        return Err(CompileError::Semantic(format!("cannot use functional update on const '{name}'")));
                    }
                    let recv_val = env.get(name).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("undefined variable: {name}"))
                    })?;
                    let method_call = Expr::MethodCall {
                        receiver: Box::new(Expr::Identifier(name.clone())),
                        method: method.clone(),
                        args: args.clone(),
                    };
                    let result = evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
                    let new_value = match (&recv_val, &result) {
                        (Value::Array(_), Value::Array(_)) => result,
                        (Value::Dict(_), Value::Dict(_)) => result,
                        (Value::Str(_), Value::Str(_)) => result,
                        (Value::Tuple(_), Value::Tuple(_)) => result,
                        (Value::Object { .. }, Value::Object { .. }) => result,
                        _ => env.get(name).cloned().unwrap_or(recv_val),
                    };
                    env.insert(name.clone(), new_value);
                    return Ok(Control::Next);
                }
                return Err(CompileError::Semantic("functional update target must be an identifier".into()));
            }
            let _ = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            Ok(Control::Next)
        }
        _ => Ok(Control::Next),
    }
}

pub(crate) fn exec_block(
    block: &Block,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    for stmt in &block.statements {
        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => return Ok(flow),
        }
    }
    Ok(Control::Next)
}

fn exec_if(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    if evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
        return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
    }
    for (cond, block) in &if_stmt.elif_branches {
        if evaluate_expr(cond, env, functions, classes, enums, impl_methods)?.truthy() {
            return exec_block(block, env, functions, classes, enums, impl_methods);
        }
    }
    if let Some(block) = &if_stmt.else_block {
        return exec_block(block, env, functions, classes, enums, impl_methods);
    }
    Ok(Control::Next)
}

fn exec_while(
    while_stmt: &simple_parser::ast::WhileStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        if !evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
            break;
        }
        match exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

fn exec_loop(
    loop_stmt: &simple_parser::ast::LoopStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        match exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

fn exec_context(
    ctx_stmt: &ContextStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let context_obj = evaluate_expr(&ctx_stmt.context, env, functions, classes, enums, impl_methods)?;
    let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));
    let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);
    result
}

fn exec_for(
    for_stmt: &simple_parser::ast::ForStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let iterable = evaluate_expr(&for_stmt.iterable, env, functions, classes, enums, impl_methods)?;
    let items = match iterable {
        Value::Object { class, fields } if class == BUILTIN_RANGE => {
            if let Some(Value::Int(start)) = fields.get("start") {
                if let Some(Value::Int(end)) = fields.get("end") {
                    let inclusive = matches!(fields.get("inclusive"), Some(Value::Bool(true)));
                    let mut v = Vec::new();
                    let mut i = *start;
                    if inclusive {
                        while i <= *end {
                            v.push(i);
                            i += 1;
                        }
                    } else {
                        while i < *end {
                            v.push(i);
                            i += 1;
                        }
                    }
                    v
                } else {
                    return Err(CompileError::Semantic("invalid range".into()));
                }
            } else {
                return Err(CompileError::Semantic("invalid range".into()));
            }
        }
        Value::Object { class, fields } if class == BUILTIN_ARRAY => {
            let mut out = Vec::new();
            for (_, v) in fields {
                if let Value::Int(i) = v {
                    out.push(i);
                }
            }
            out
        }
        _ => return Err(CompileError::Semantic("for expects range or array".into())),
    };

    for val in items {
        if let Pattern::Identifier(name) = &for_stmt.pattern {
            env.insert(name.clone(), Value::Int(val));
        }
        match exec_block(&for_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

fn exec_match(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let subject = evaluate_expr(&match_stmt.subject, env, functions, classes, enums, impl_methods)?;

    for arm in &match_stmt.arms {
        let mut bindings = HashMap::new();
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums)? {
            if let Some(guard) = &arm.guard {
                let mut guard_env = env.clone();
                for (name, value) in &bindings {
                    guard_env.insert(name.clone(), value.clone());
                }
                if !evaluate_expr(guard, &guard_env, functions, classes, enums, impl_methods)?.truthy() {
                    continue;
                }
            }

            for (name, value) in bindings {
                env.insert(name, value);
            }

            return exec_block(&arm.body, env, functions, classes, enums, impl_methods);
        }
    }

    Ok(Control::Next)
}

fn pattern_matches(
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
) -> Result<bool, CompileError> {
    match pattern {
        Pattern::Wildcard => Ok(true),

        Pattern::Identifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MutIdentifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::Literal(lit_expr) => {
            match lit_expr.as_ref() {
                Expr::Integer(i) => {
                    if let Value::Int(v) = value {
                        Ok(*v == *i)
                    } else {
                        Ok(false)
                    }
                }
                Expr::String(s) => {
                    if let Value::Str(v) = value {
                        Ok(v == s)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Symbol(sym) => {
                    if let Value::Symbol(v) = value {
                        Ok(v == sym)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Bool(b) => {
                    if let Value::Bool(v) = value {
                        Ok(*v == *b)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Nil => Ok(matches!(value, Value::Nil)),
                _ => Ok(false),
            }
        }

        Pattern::Enum { name: enum_name, variant, payload } => {
            if let Value::Enum { enum_name: ve, variant: vv, payload: value_payload } = value {
                if enum_name == ve && variant == vv {
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        if patterns.len() == 1 {
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)? {
                                return Ok(true);
                            }
                        }
                    }
                    if payload.is_none() && value_payload.is_some() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        Pattern::Tuple(patterns) => {
            if let Value::Tuple(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Array(patterns) => {
            if let Value::Array(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Struct { name, fields } => {
            if let Value::Object { class, fields: obj_fields } = value {
                if class == name {
                    for (field_name, field_pat) in fields {
                        if let Some(field_val) = obj_fields.get(field_name) {
                            if !pattern_matches(field_pat, field_val, bindings, enums)? {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Or(patterns) => {
            for pat in patterns {
                let mut temp_bindings = HashMap::new();
                if pattern_matches(pat, value, &mut temp_bindings, enums)? {
                    bindings.extend(temp_bindings);
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Typed { pattern, ty } => {
            let type_matches = match ty {
                Type::Simple(name) => value.matches_type(name),
                Type::Union(types) => {
                    types.iter().any(|t| {
                        if let Type::Simple(name) = t {
                            value.matches_type(name)
                        } else {
                            true
                        }
                    })
                }
                _ => true,
            };

            if type_matches {
                pattern_matches(pattern, value, bindings, enums)
            } else {
                Ok(false)
            }
        }

        Pattern::Rest => {
            Ok(true)
        }
    }
}

/// Evaluate a constant expression at compile time
#[instrument(skip(env, functions, classes, enums, impl_methods))]
pub(crate) fn evaluate_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(Value::Int(*value)),
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Nil => Ok(Value::Nil),
        Expr::String(s) => Ok(Value::Str(s.clone())),
        Expr::FString(parts) => {
            let mut out = String::new();
            for part in parts {
                match part {
                    FStringPart::Literal(lit) => out.push_str(lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        out.push_str(&v.to_display_string());
                    }
                }
            }
            Ok(Value::Str(out))
        }
        Expr::Symbol(s) => Ok(Value::Symbol(s.clone())),
        Expr::Identifier(name) => {
            if name == "None" {
                return Ok(Value::Enum {
                    enum_name: "Option".into(),
                    variant: "None".into(),
                    payload: None,
                });
            }
            env.get(name)
                .cloned()
                .ok_or_else(|| CompileError::Semantic(format!("undefined variable: {name}")))
        },
        Expr::New { kind, expr } => {
            let inner = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            match kind {
                PointerKind::Unique => Ok(Value::Unique(ManualUniqueValue::new(inner))),
                PointerKind::Shared => Ok(Value::Shared(ManualSharedValue::new(inner))),
                PointerKind::Weak => {
                    if let Value::Shared(shared) = inner {
                        Ok(Value::Weak(ManualWeakValue::new_from_shared(&shared)))
                    } else {
                        Err(CompileError::Semantic(
                            "new - expects a shared pointer to create a weak reference".into(),
                        ))
                    }
                }
                PointerKind::Handle => Ok(Value::Handle(ManualHandleValue::new(inner))),
                PointerKind::Borrow => Ok(Value::Borrow(BorrowValue::new(inner))),
                PointerKind::BorrowMut => Ok(Value::BorrowMut(BorrowMutValue::new(inner))),
            }
        }
        Expr::Binary { op, left, right } => {
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
            match op {
                BinOp::Add => match (left_val, right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
                    (Value::Str(a), b) => Ok(Value::Str(format!("{a}{}", b.to_display_string()))),
                    (a, Value::Str(b)) => Ok(Value::Str(format!("{}{}", a.to_display_string(), b))),
                    (l, r) => Ok(Value::Int(l.as_int()? + r.as_int()?)),
                },
                BinOp::Sub => Ok(Value::Int(left_val.as_int()? - right_val.as_int()?)),
                BinOp::Mul => Ok(Value::Int(left_val.as_int()? * right_val.as_int()?)),
                BinOp::Div => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("division by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? / r))
                    }
                }
                BinOp::Mod => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("modulo by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? % r))
                    }
                }
                BinOp::Eq => Ok(Value::Bool(left_val == right_val)),
                BinOp::NotEq => Ok(Value::Bool(left_val != right_val)),
                BinOp::Lt => Ok(Value::Bool(left_val.as_int()? < right_val.as_int()?)),
                BinOp::Gt => Ok(Value::Bool(left_val.as_int()? > right_val.as_int()?)),
                BinOp::LtEq => Ok(Value::Bool(left_val.as_int()? <= right_val.as_int()?)),
                BinOp::GtEq => Ok(Value::Bool(left_val.as_int()? >= right_val.as_int()?)),
                BinOp::Is => Ok(Value::Bool(left_val == right_val)),
                BinOp::And => Ok(Value::Bool(left_val.truthy() && right_val.truthy())),
                BinOp::Or => Ok(Value::Bool(left_val.truthy() || right_val.truthy())),
                BinOp::Pow => {
                    let base = left_val.as_int()?;
                    let exp = right_val.as_int()?;
                    if exp < 0 {
                        Err(CompileError::Semantic("negative exponent not supported for integers".into()))
                    } else {
                        Ok(Value::Int(base.pow(exp as u32)))
                    }
                }
                BinOp::FloorDiv => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("floor division by zero".into()))
                    } else {
                        let l = left_val.as_int()?;
                        // Floor division: always round towards negative infinity
                        Ok(Value::Int(l.div_euclid(r)))
                    }
                }
                BinOp::BitAnd => Ok(Value::Int(left_val.as_int()? & right_val.as_int()?)),
                BinOp::BitOr => Ok(Value::Int(left_val.as_int()? | right_val.as_int()?)),
                BinOp::BitXor => Ok(Value::Int(left_val.as_int()? ^ right_val.as_int()?)),
                BinOp::ShiftLeft => Ok(Value::Int(left_val.as_int()? << right_val.as_int()?)),
                BinOp::ShiftRight => Ok(Value::Int(left_val.as_int()? >> right_val.as_int()?)),
                BinOp::In => {
                    // Membership test: check if left is in right (array, tuple, dict, or string)
                    match right_val {
                        Value::Array(arr) => Ok(Value::Bool(arr.contains(&left_val))),
                        Value::Tuple(tup) => Ok(Value::Bool(tup.contains(&left_val))),
                        Value::Dict(dict) => {
                            let key = left_val.to_key_string();
                            Ok(Value::Bool(dict.contains_key(&key)))
                        }
                        Value::Str(s) => {
                            let needle = left_val.to_key_string();
                            Ok(Value::Bool(s.contains(&needle)))
                        }
                        _ => Err(CompileError::Semantic("'in' operator requires array, tuple, dict, or string".into())),
                    }
                }
            }
        }
        Expr::Unary { op, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)?;
            match op {
                UnaryOp::Neg => Ok(Value::Int(-val.as_int()?)),
                UnaryOp::Not => Ok(Value::Bool(!val.truthy())),
                UnaryOp::BitNot => Ok(Value::Int(!val.as_int()?)),
                UnaryOp::Ref => Ok(Value::Borrow(BorrowValue::new(val))),
                UnaryOp::RefMut => Ok(Value::BorrowMut(BorrowMutValue::new(val))),
                UnaryOp::Deref => Ok(val.deref_pointer()),
            }
        }
        Expr::Lambda { params, body } => {
            let names: Vec<String> = params.iter().map(|LambdaParam { name, .. }| name.clone()).collect();
            Ok(Value::Lambda { params: names, body: body.clone(), env: env.clone() })
        }
        Expr::If { condition, then_branch, else_branch } => {
            if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)
            } else {
                Ok(Value::Nil)
            }
        }
        Expr::Call { callee, args } => {
            evaluate_call(callee, args, env, functions, classes, enums, impl_methods)
        }
        Expr::MethodCall { receiver, method, args } => {
            evaluate_method_call(receiver, method, args, env, functions, classes, enums, impl_methods)
        }
        Expr::FieldAccess { receiver, field } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            if let Value::Object { fields, .. } = recv_val {
                fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| CompileError::Semantic(format!("unknown field {field}")))
            } else {
                Err(CompileError::Semantic("field access on non-object".into()))
            }
        }
        Expr::StructInit { name, fields } => {
            let mut map = HashMap::new();
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
            Ok(Value::Object {
                class: name.clone(),
                fields: map,
            })
        }
        Expr::Path(segments) => {
            if segments.len() == 2 {
                let enum_name = &segments[0];
                let variant = &segments[1];
                if let Some(variants) = enums.get(enum_name) {
                    if variants.contains(variant) {
                        Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: variant.clone(),
                            payload: None,
                        })
                    } else {
                        Err(CompileError::Semantic(format!(
                            "unknown variant {variant} for enum {enum_name}"
                        )))
                    }
                } else {
                    Err(CompileError::Semantic(format!("unknown enum: {enum_name}")))
                }
            } else {
                Err(CompileError::Semantic(format!(
                    "unsupported path: {:?}",
                    segments
                )))
            }
        }
        Expr::Dict(entries) => {
            let mut map = HashMap::new();
            for (k, v) in entries {
                let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                map.insert(key_val.to_key_string(), val);
            }
            Ok(Value::Dict(map))
        }
        Expr::Range { start, end, bound } => {
            let start = start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            let end = end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            Ok(create_range_object(start, end, *bound))
        }
        Expr::Array(items) => {
            let mut arr = Vec::new();
            for item in items {
                arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Array(arr))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Tuple(tup))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
            match recv_val {
                Value::Array(arr) => {
                    let idx = idx_val.as_int()? as usize;
                    arr.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("array index out of bounds: {idx}")))
                }
                Value::Tuple(tup) => {
                    let idx = idx_val.as_int()? as usize;
                    tup.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("tuple index out of bounds: {idx}")))
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    map.get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
                }
                Value::Str(s) => {
                    let idx = idx_val.as_int()? as usize;
                    s.chars()
                        .nth(idx)
                        .map(|c| Value::Str(c.to_string()))
                        .ok_or_else(|| CompileError::Semantic(format!("string index out of bounds: {idx}")))
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic("index access on non-indexable type".into())),
            }
        }
        Expr::Spawn(inner) => {
            Ok(spawn_actor_with_expr(inner, env, functions, classes, enums, impl_methods))
        }
        Expr::Await(inner) => {
            check_waitless_violation("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => {
                    f.await_result().map_err(|e| CompileError::Semantic(e))
                }
                Value::Actor(handle) => {
                    handle.join().map_err(|e| CompileError::Semantic(e))?;
                    Ok(Value::Nil)
                }
                other => Ok(other),
            }
        }
        Expr::Yield(maybe_val) => {
            let yield_val = match maybe_val {
                Some(expr) => evaluate_expr(expr, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };

            let added = GENERATOR_YIELDS.with(|cell| {
                if let Some(yields) = cell.borrow_mut().as_mut() {
                    yields.push(yield_val.clone());
                    true
                } else {
                    false
                }
            });

            if !added {
                return Err(CompileError::Semantic("yield called outside of generator".into()));
            }

            Ok(Value::Nil)
        }
        Expr::FunctionalUpdate { target, method, args } => {
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
        }
        Expr::MacroInvocation { name, args: macro_args } => {
            evaluate_macro_invocation(name, macro_args, env, functions, classes, enums, impl_methods)
        }
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}

// ============================================================================
// Helper functions to reduce duplication across interpreter modules
// ============================================================================

/// Build method_missing arguments from method name and original args
fn build_method_missing_args(method: &str, args: &[simple_parser::ast::Argument]) -> Vec<simple_parser::ast::Argument> {
    vec![
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Symbol(method.to_string()),
        },
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
        },
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Nil,
        },
    ]
}

/// Find and execute a method on a class/struct object.
/// Searches in class_def methods first, then impl_methods.
/// Returns Ok(Some(value)) if method found, Ok(None) if not found.
fn find_and_exec_method<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class) {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
            return Ok(Some(exec_function(func, args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method) {
            return Ok(Some(exec_function(func, args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    Ok(None)
}

/// Try to call method_missing hook on a class/struct object.
/// Returns Ok(Some(value)) if method_missing found, Ok(None) if not found.
fn try_method_missing<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let mm_args = build_method_missing_args(method, args);
    // Check class methods for method_missing
    if let Some(class_def) = classes.get(class) {
        if let Some(mm_func) = class_def.methods.iter().find(|m| m.name == "method_missing") {
            return Ok(Some(exec_function(mm_func, &mm_args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    // Check impl methods for method_missing
    if let Some(methods) = impl_methods.get(class) {
        if let Some(mm_func) = methods.iter().find(|m| m.name == "method_missing") {
            return Ok(Some(exec_function(mm_func, &mm_args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    Ok(None)
}

/// Create a range object with start, end, and bound type fields.
/// The bound is stored as a boolean for runtime compatibility.
fn create_range_object(start: i64, end: i64, bound: RangeBound) -> Value {
    let mut fields = HashMap::new();
    fields.insert("start".into(), Value::Int(start));
    fields.insert("end".into(), Value::Int(end));
    // Store as boolean for runtime iteration compatibility
    fields.insert("inclusive".into(), Value::Bool(bound.is_inclusive()));
    Value::Object {
        class: BUILTIN_RANGE.into(),
        fields,
    }
}

/// Spawn an actor with the given expression and environment
fn spawn_actor_with_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Value {
    let expr_clone = expr.clone();
    let env_clone = env.clone();
    let funcs = functions.clone();
    let classes_clone = classes.clone();
    let enums_clone = enums.clone();
    let impls_clone = impl_methods.clone();
    let handle = ACTOR_SPAWNER.with(|s| s.spawn(move |inbox, outbox| {
        let inbox = Arc::new(Mutex::new(inbox));
        ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
        ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));
        let _ = evaluate_expr(&expr_clone, &env_clone, &funcs, &classes_clone, &enums_clone, &impls_clone);
        ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
        ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
    }));
    Value::Actor(handle)
}

/// Evaluate an optional argument at given index with a default value.
/// This is a common pattern in method calls: args.get(idx).map(eval).transpose()?.unwrap_or(default)
fn eval_arg(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: Value,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    args.get(idx)
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .transpose()
        .map(|opt| opt.unwrap_or(default))
}

/// Evaluate an argument as i64 with default
fn eval_arg_int(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: i64,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<i64, CompileError> {
    eval_arg(args, idx, Value::Int(default), env, functions, classes, enums, impl_methods)?
        .as_int()
}

/// Evaluate an argument as usize with default
fn eval_arg_usize(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: usize,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<usize, CompileError> {
    Ok(eval_arg_int(args, idx, default as i64, env, functions, classes, enums, impl_methods)? as usize)
}

/// Apply a lambda to each item in an array, returning Vec of results.
fn apply_lambda_to_vec(
    arr: &[Value],
    lambda_val: &Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Value>, CompileError> {
    if let Value::Lambda { params, body, env: captured } = lambda_val {
        let mut results = Vec::new();
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            results.push(result);
        }
        Ok(results)
    } else {
        Err(CompileError::Semantic("expected lambda argument".into()))
    }
}

/// Array map: apply lambda to each element
fn eval_array_map(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let results = apply_lambda_to_vec(arr, &func, functions, classes, enums, impl_methods)?;
    Ok(Value::Array(results))
}

/// Array filter: keep elements where lambda returns truthy
fn eval_array_filter(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut results = Vec::new();
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let keep = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            if keep.truthy() {
                results.push(item.clone());
            }
        }
        Ok(Value::Array(results))
    } else {
        Err(CompileError::Semantic("filter expects lambda argument".into()))
    }
}

/// Array reduce: fold over elements with accumulator
fn eval_array_reduce(
    arr: &[Value],
    init: Value,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut acc = init;
        for item in arr {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), acc);
                local_env.insert(params[1].clone(), item.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            acc = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
        }
        Ok(acc)
    } else {
        Err(CompileError::Semantic("reduce expects lambda argument".into()))
    }
}

/// Array find: return first element where lambda is truthy
fn eval_array_find(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let matches = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            if matches.truthy() {
                return Ok(item.clone());
            }
        }
        Ok(Value::Nil)
    } else {
        Err(CompileError::Semantic("find expects lambda argument".into()))
    }
}

/// Array any: return true if any element satisfies lambda
fn eval_array_any(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            if result.truthy() {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    } else {
        Err(CompileError::Semantic("any expects lambda argument".into()))
    }
}

/// Array all: return true if all elements satisfy lambda
fn eval_array_all(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            if !result.truthy() {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    } else {
        Err(CompileError::Semantic("all expects lambda argument".into()))
    }
}

/// Dict map_values: apply lambda to each value
fn eval_dict_map_values(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), v.clone());
            }
            let new_val = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            new_map.insert(k.clone(), new_val);
        }
        Ok(Value::Dict(new_map))
    } else {
        Err(CompileError::Semantic("map_values expects lambda argument".into()))
    }
}

/// Dict filter: keep entries where lambda returns truthy
fn eval_dict_filter(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), Value::Str(k.clone()));
                local_env.insert(params[1].clone(), v.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), v.clone());
            }
            let keep = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            if keep.truthy() {
                new_map.insert(k.clone(), v.clone());
            }
        }
        Ok(Value::Dict(new_map))
    } else {
        Err(CompileError::Semantic("filter expects lambda argument".into()))
    }
}

/// Convert a Message to a Value
fn message_to_value(msg: Message) -> Value {
    match msg {
        Message::Value(s) => Value::Str(s),
        Message::Bytes(b) => Value::Str(String::from_utf8_lossy(&b).to_string()),
    }
}

/// Option map: apply lambda to Some value
fn eval_option_map(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if variant == "Some" {
        if let Some(val) = payload {
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda { params, body, env: captured } = func_arg {
                let mut local_env = captured.clone();
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), val.as_ref().clone());
                }
                let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Enum {
                    enum_name: "Option".into(),
                    variant: "Some".into(),
                    payload: Some(Box::new(result)),
                });
            }
        }
    }
    Ok(Value::Enum {
        enum_name: "Option".into(),
        variant: "None".into(),
        payload: None,
    })
}

// Include the rest of the interpreter functions
include!("interpreter_call.rs");
include!("interpreter_method.rs");
include!("interpreter_macro.rs");
include!("interpreter_extern.rs");
include!("interpreter_context.rs");
