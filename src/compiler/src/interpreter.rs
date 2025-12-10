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
use std::sync::{mpsc, Arc, Mutex};

use simple_common::actor::{ActorSpawner, Message, ThreadSpawner};
use simple_parser::ast::{
    AssignOp, BinOp, Block, ClassDef, ContextStmt, Effect, EnumDef, Expr, ExternDef, FStringPart,
    FunctionDef, IfStmt, LambdaParam, MacroArg, MacroBody, MacroDef, MacroParam, MatchStmt, Node,
    Pattern, PointerKind, RangeBound, Type, UnaryOp, UnitDef, WithStmt,
};
use tracing::instrument;

use crate::effects::{check_async_violation, CURRENT_EFFECT};
use crate::error::CompileError;
use crate::value::{
    BorrowMutValue, BorrowValue, Env, FutureValue, GeneratorValue, ManualHandleValue,
    ManualSharedValue, ManualUniqueValue, ManualWeakValue, Value, BUILTIN_ARRAY, BUILTIN_RANGE,
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

/// Stores enum definitions: name -> EnumDef
pub(crate) type Enums = HashMap<String, EnumDef>;

/// Stores impl block methods: type_name -> list of methods
pub(crate) type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Stores extern function declarations: name -> definition
pub(crate) type ExternFunctions = HashMap<String, ExternDef>;

/// Stores macro definitions: name -> definition
pub(crate) type Macros = HashMap<String, MacroDef>;

/// Stores unit type definitions: suffix -> UnitDef
pub(crate) type Units = HashMap<String, UnitDef>;

/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(Value),
    Break(Option<Value>),
    Continue,
}

/// Call a value (function or lambda) with evaluated arguments.
/// Used for decorator application where we have Value arguments, not AST Arguments.
fn call_value_with_args(
    callee: &Value,
    args: Vec<Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match callee {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            // Execute lambda with given args
            let mut local_env = captured.clone();
            for (i, param) in params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    local_env.insert(param.clone(), arg.clone());
                }
            }
            evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
        }
        Value::Function {
            def, captured_env, ..
        } => {
            // Execute function with given args, using the captured environment for closure
            let mut local_env = captured_env.clone();
            for (i, param) in def.params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    local_env.insert(param.name.clone(), arg.clone());
                }
            }
            // Execute the function body
            let result = exec_block(
                &def.body,
                &mut local_env,
                functions,
                classes,
                enums,
                impl_methods,
            );
            match result {
                Ok(Control::Return(v)) => Ok(v),
                Ok(Control::Next) => Ok(Value::Nil),
                Ok(Control::Break(_)) => Err(CompileError::Semantic("break outside loop".into())),
                Ok(Control::Continue) => {
                    Err(CompileError::Semantic("continue outside loop".into()))
                }
                Err(e) => Err(e),
            }
        }
        _ => Err(CompileError::Semantic(format!(
            "cannot call value of type {}",
            callee.type_name()
        ))),
    }
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
    let mut units: Units = HashMap::new();

    // First pass: register all functions (needed for decorator lookup)
    for item in items {
        match item {
            Node::Function(f) => {
                functions.insert(f.name.clone(), f.clone());
            }
            _ => {}
        }
    }

    // Second pass: apply decorators and register other items
    for item in items {
        match item {
            Node::Function(f) => {
                // If function has decorators, apply them
                if !f.decorators.is_empty() {
                    // Create a function value from the original function
                    // For top-level functions, captured_env is empty (they don't capture anything)
                    let func_value = Value::Function {
                        name: f.name.clone(),
                        def: Box::new(f.clone()),
                        captured_env: Env::new(),
                    };

                    // Apply decorators in reverse order (bottom-to-top, outermost last)
                    let mut decorated = func_value;
                    for decorator in f.decorators.iter().rev() {
                        // Evaluate the decorator expression
                        let decorator_fn = evaluate_expr(
                            &decorator.name,
                            &env,
                            &functions,
                            &classes,
                            &enums,
                            &impl_methods,
                        )?;

                        // If decorator has arguments, call it first to get the actual decorator
                        let actual_decorator = if let Some(args) = &decorator.args {
                            let mut arg_values = vec![];
                            for arg in args {
                                arg_values.push(evaluate_expr(
                                    arg,
                                    &env,
                                    &functions,
                                    &classes,
                                    &enums,
                                    &impl_methods,
                                )?);
                            }
                            call_value_with_args(
                                &decorator_fn,
                                arg_values,
                                &env,
                                &functions,
                                &classes,
                                &enums,
                                &impl_methods,
                            )?
                        } else {
                            decorator_fn
                        };

                        // Call the decorator with the current function value
                        decorated = call_value_with_args(
                            &actual_decorator,
                            vec![decorated],
                            &env,
                            &functions,
                            &classes,
                            &enums,
                            &impl_methods,
                        )?;
                    }

                    // Store the decorated result in the env
                    env.insert(f.name.clone(), decorated);
                }
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
                enums.insert(e.name.clone(), e.clone());
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
                classes.insert(
                    a.name.clone(),
                    ClassDef {
                        span: a.span,
                        name: a.name.clone(),
                        generic_params: Vec::new(),
                        fields: a.fields.clone(),
                        methods: a.methods.clone(),
                        parent: None,
                        visibility: a.visibility,
                        attributes: vec![],
                    },
                );
                env.insert(
                    a.name.clone(),
                    Value::Object {
                        class: a.name.clone(),
                        fields: HashMap::new(),
                    },
                );
            }
            Node::TypeAlias(t) => {
                // Type aliases are handled at type-check time
                // Store the alias name for reference
                env.insert(t.name.clone(), Value::Nil);
            }
            Node::Unit(u) => {
                // Unit types define a newtype wrapper with a literal suffix
                // Register the unit type name and its suffix for later use
                units.insert(u.suffix.clone(), u.clone());
                env.insert(u.name.clone(), Value::Nil);
            }
            Node::Let(_)
            | Node::Const(_)
            | Node::Static(_)
            | Node::Assignment(_)
            | Node::If(_)
            | Node::For(_)
            | Node::While(_)
            | Node::Loop(_)
            | Node::Match(_)
            | Node::Context(_)
            | Node::With(_) => {
                if let Control::Return(val) =
                    exec_node(item, &mut env, &functions, &classes, &enums, &impl_methods)?
                {
                    return val.as_int().map(|v| v as i32);
                }
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let val =
                        evaluate_expr(expr, &env, &functions, &classes, &enums, &impl_methods)?;
                    return val.as_int().map(|v| v as i32);
                }
                return Ok(0);
            }
            Node::Expression(expr) => {
                if let Expr::FunctionalUpdate {
                    target,
                    method,
                    args,
                } = expr
                {
                    if let Expr::Identifier(name) = target.as_ref() {
                        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                        if is_const {
                            return Err(CompileError::Semantic(format!(
                                "cannot use functional update on const '{name}'"
                            )));
                        }
                        let recv_val = env.get(name).cloned().ok_or_else(|| {
                            CompileError::Semantic(format!("undefined variable: {name}"))
                        })?;
                        let method_call = Expr::MethodCall {
                            receiver: Box::new(Expr::Identifier(name.clone())),
                            method: method.clone(),
                            args: args.clone(),
                        };
                        let result = evaluate_expr(
                            &method_call,
                            &env,
                            &functions,
                            &classes,
                            &enums,
                            &impl_methods,
                        )?;
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
                    return Err(CompileError::Semantic(
                        "functional update target must be an identifier".into(),
                    ));
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

    let main_val = env.get("main").cloned().unwrap_or(Value::Int(0)).as_int()? as i32;
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
                let value =
                    evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                if let Pattern::Identifier(name) = &let_stmt.pattern {
                    env.insert(name.clone(), value);
                    if !let_stmt.mutability.is_mutable() {
                        CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                    }
                } else if let Pattern::MutIdentifier(name) = &let_stmt.pattern {
                    env.insert(name.clone(), value);
                } else if let Pattern::Tuple(patterns) = &let_stmt.pattern {
                    // Allow tuple pattern to match both Tuple and Array
                    let values: Vec<Value> = match value {
                        Value::Tuple(v) => v,
                        Value::Array(v) => v,
                        _ => Vec::new(),
                    };
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
            let value = evaluate_expr(
                &const_stmt.value,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            env.insert(const_stmt.name.clone(), value);
            CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
            Ok(Control::Next)
        }
        Node::Static(static_stmt) => {
            let value = evaluate_expr(
                &static_stmt.value,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
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
                    return Err(CompileError::Semantic(format!(
                        "cannot assign to const '{name}'"
                    )));
                }
                let value =
                    evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                env.insert(name.clone(), value);
                Ok(Control::Next)
            } else if let Expr::FieldAccess { receiver, field } = &assign.target {
                // Handle field assignment: obj.field = value
                let value =
                    evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                // Get the object name (must be an identifier for now)
                if let Expr::Identifier(obj_name) = receiver.as_ref() {
                    if let Some(obj_val) = env.get(obj_name).cloned() {
                        match obj_val {
                            Value::Object { class, mut fields } => {
                                fields.insert(field.clone(), value);
                                env.insert(obj_name.clone(), Value::Object { class, fields });
                            }
                            _ => {
                                return Err(CompileError::Semantic(format!(
                                    "cannot assign field on non-object value"
                                )))
                            }
                        }
                        Ok(Control::Next)
                    } else {
                        Err(CompileError::Semantic(format!(
                            "undefined variable '{obj_name}'"
                        )))
                    }
                } else {
                    Err(CompileError::Semantic(
                        "field assignment requires identifier as object".into(),
                    ))
                }
            } else {
                Err(CompileError::Semantic(
                    "unsupported assignment target".into(),
                ))
            }
        }
        Node::If(if_stmt) => exec_if(if_stmt, env, functions, classes, enums, impl_methods),
        Node::While(while_stmt) => {
            exec_while(while_stmt, env, functions, classes, enums, impl_methods)
        }
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
                Some(evaluate_expr(
                    expr,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?)
            } else {
                None
            };
            Ok(Control::Break(value))
        }
        Node::Continue(_) => Ok(Control::Continue),
        Node::Match(match_stmt) => {
            exec_match(match_stmt, env, functions, classes, enums, impl_methods)
        }
        Node::Context(ctx_stmt) => {
            exec_context(ctx_stmt, env, functions, classes, enums, impl_methods)
        }
        Node::With(with_stmt) => exec_with(with_stmt, env, functions, classes, enums, impl_methods),
        Node::Expression(expr) => {
            if let Expr::FunctionalUpdate {
                target,
                method,
                args,
            } = expr
            {
                if let Expr::Identifier(name) = target.as_ref() {
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                    if is_const {
                        return Err(CompileError::Semantic(format!(
                            "cannot use functional update on const '{name}'"
                        )));
                    }
                    let recv_val = env.get(name).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("undefined variable: {name}"))
                    })?;
                    let method_call = Expr::MethodCall {
                        receiver: Box::new(Expr::Identifier(name.clone())),
                        method: method.clone(),
                        args: args.clone(),
                    };
                    let result =
                        evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
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
                return Err(CompileError::Semantic(
                    "functional update target must be an identifier".into(),
                ));
            }
            let _ = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
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

// Include control flow functions (if, while, loop, for, match, pattern_matches)
include!("interpreter_control.rs");

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
        Expr::TypedInteger(value, _suffix) => {
            // For now, we treat typed integers the same as regular integers
            // The type suffix is used for type checking, not runtime behavior
            Ok(Value::Int(*value))
        }
        Expr::Float(value) => Ok(Value::Float(*value)),
        Expr::TypedFloat(value, _suffix) => {
            // For now, we treat typed floats the same as regular floats
            Ok(Value::Float(*value))
        }
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
            // First check env for local variables and closures
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            // Then check functions for top-level function definitions
            // Return as Value::Function for first-class function usage
            if let Some(func) = functions.get(name) {
                return Ok(Value::Function {
                    name: name.clone(),
                    def: Box::new(func.clone()),
                    captured_env: Env::new(), // Top-level functions don't capture
                });
            }
            // Check classes - return as Constructor for constructor polymorphism
            if classes.contains_key(name) {
                return Ok(Value::Constructor {
                    class_name: name.clone(),
                });
            }
            Err(CompileError::Semantic(format!(
                "undefined variable: {name}"
            )))
        }
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
                        Err(CompileError::Semantic(
                            "negative exponent not supported for integers".into(),
                        ))
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
                        _ => Err(CompileError::Semantic(
                            "'in' operator requires array, tuple, dict, or string".into(),
                        )),
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
            let names: Vec<String> = params
                .iter()
                .map(|LambdaParam { name, .. }| name.clone())
                .collect();
            Ok(Value::Lambda {
                params: names,
                body: body.clone(),
                env: env.clone(),
            })
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
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
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => evaluate_method_call(
            receiver,
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::FieldAccess { receiver, field } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
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
                if let Some(enum_def) = enums.get(enum_name) {
                    if enum_def.variants.iter().any(|v| &v.name == variant) {
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
                // Handle dict spread: **expr
                if let Expr::DictSpread(inner) = k {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(spread_map) = spread_val {
                        for (sk, sv) in spread_map {
                            map.insert(sk, sv);
                        }
                    } else {
                        return Err(CompileError::Semantic(
                            "dict spread requires dict value".into(),
                        ));
                    }
                } else {
                    let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                    let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                    map.insert(key_val.to_key_string(), val);
                }
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
                // Handle spread operator: *expr
                if let Expr::Spread(inner) = item {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    match spread_val {
                        Value::Array(spread_arr) => arr.extend(spread_arr),
                        Value::Tuple(tup) => arr.extend(tup),
                        _ => {
                            return Err(CompileError::Semantic(
                                "spread operator requires array or tuple".into(),
                            ))
                        }
                    }
                } else {
                    arr.push(evaluate_expr(
                        item,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?);
                }
            }
            Ok(Value::Array(arr))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(
                    item,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?);
            }
            Ok(Value::Tuple(tup))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
            match recv_val {
                Value::Array(arr) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("array index out of bounds: {raw_idx}"))
                    })
                }
                Value::Tuple(tup) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = tup.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    tup.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("tuple index out of bounds: {raw_idx}"))
                    })
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    map.get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
                }
                Value::Str(s) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = s.chars().count() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    s.chars()
                        .nth(idx)
                        .map(|c| Value::Str(c.to_string()))
                        .ok_or_else(|| {
                            CompileError::Semantic(format!("string index out of bounds: {raw_idx}"))
                        })
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic(
                    "index access on non-indexable type".into(),
                )),
            }
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let mut result = Vec::new();

            let items = iter_to_vec(&iter_val)?;
            for item in items {
                // Create a new scope with the pattern binding
                let mut inner_env = env.clone();
                if !bind_pattern(pattern, &item, &mut inner_env) {
                    continue;
                }

                // Check condition if present
                if let Some(cond) = condition {
                    let cond_val = evaluate_expr(
                        cond,
                        &mut inner_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    if !cond_val.truthy() {
                        continue;
                    }
                }

                // Evaluate the expression
                let val = evaluate_expr(
                    expr,
                    &mut inner_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                result.push(val);
            }
            Ok(Value::Array(result))
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let mut result = HashMap::new();

            let items = iter_to_vec(&iter_val)?;
            for item in items {
                // Create a new scope with the pattern binding
                let mut inner_env = env.clone();
                if !bind_pattern(pattern, &item, &mut inner_env) {
                    continue;
                }

                // Check condition if present
                if let Some(cond) = condition {
                    let cond_val = evaluate_expr(
                        cond,
                        &mut inner_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    if !cond_val.truthy() {
                        continue;
                    }
                }

                // Evaluate key and value
                let k =
                    evaluate_expr(key, &mut inner_env, functions, classes, enums, impl_methods)?;
                let v = evaluate_expr(
                    value,
                    &mut inner_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                result.insert(k.to_key_string(), v);
            }
            Ok(Value::Dict(result))
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            let len = match &recv_val {
                Value::Array(arr) => arr.len() as i64,
                Value::Str(s) => s.len() as i64,
                Value::Tuple(t) => t.len() as i64,
                _ => return Err(CompileError::Semantic("slice on non-sliceable type".into())),
            };

            // Parse start, end, step with Python-style semantics
            let start_idx = if let Some(s) = start {
                let v = evaluate_expr(s, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                0
            };

            let end_idx = if let Some(e) = end {
                let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                len
            };

            let step_val = if let Some(st) = step {
                evaluate_expr(st, env, functions, classes, enums, impl_methods)?.as_int()?
            } else {
                1
            };

            if step_val == 0 {
                return Err(CompileError::Semantic("slice step cannot be zero".into()));
            }

            match recv_val {
                Value::Array(arr) => Ok(Value::Array(slice_collection(
                    &arr, start_idx, end_idx, step_val,
                ))),
                Value::Str(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    let sliced = slice_collection(&chars, start_idx, end_idx, step_val);
                    Ok(Value::Str(sliced.into_iter().collect()))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(
                    &tup, start_idx, end_idx, step_val,
                ))),
                _ => Err(CompileError::Semantic("slice on non-sliceable type".into())),
            }
        }
        Expr::Spread(inner) => {
            // Spread is handled by Array/Dict evaluation, but standalone should work too
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::DictSpread(inner) => {
            // DictSpread is handled by Dict evaluation
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::Spawn(inner) => Ok(spawn_actor_with_expr(
            inner,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )),
        Expr::Await(inner) => {
            check_async_violation("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => f.await_result().map_err(|e| CompileError::Semantic(e)),
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
                return Err(CompileError::Semantic(
                    "yield called outside of generator".into(),
                ));
            }

            Ok(Value::Nil)
        }
        Expr::FunctionalUpdate {
            target,
            method,
            args,
        } => {
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
        }
        Expr::MacroInvocation {
            name,
            args: macro_args,
        } => evaluate_macro_invocation(
            name,
            macro_args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::Try(inner) => {
            // Try operator: expr? - unwrap Ok or propagate Err
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Enum {
                    enum_name,
                    variant,
                    payload,
                } if enum_name == "Result" => {
                    match variant.as_str() {
                        "Ok" => {
                            if let Some(inner_val) = payload {
                                Ok(*inner_val)
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        "Err" => {
                            // Return the Err as a TryError that should be propagated
                            Err(CompileError::TryError(Value::Enum {
                                enum_name,
                                variant,
                                payload,
                            }))
                        }
                        _ => Err(CompileError::Semantic(format!(
                            "invalid Result variant: {}",
                            variant
                        ))),
                    }
                }
                Value::Enum {
                    enum_name,
                    variant,
                    payload,
                } if enum_name == "Option" => {
                    match variant.as_str() {
                        "Some" => {
                            if let Some(inner_val) = payload {
                                Ok(*inner_val)
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        "None" => {
                            // Return None as a TryError
                            Err(CompileError::TryError(Value::Enum {
                                enum_name,
                                variant,
                                payload,
                            }))
                        }
                        _ => Err(CompileError::Semantic(format!(
                            "invalid Option variant: {}",
                            variant
                        ))),
                    }
                }
                _ => Err(CompileError::Semantic(
                    "? operator requires Result or Option type".into(),
                )),
            }
        }
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}

// Include helper functions (method dispatch, array/dict ops, pattern binding, slicing)
include!("interpreter_helpers.rs");

// Include the rest of the interpreter functions
include!("interpreter_call.rs");
include!("interpreter_method.rs");
include!("interpreter_macro.rs");
include!("interpreter_extern.rs");
include!("interpreter_context.rs");
