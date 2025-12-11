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
    AssignOp, BinOp, Block, ClassDef, ContextStmt, EnumDef, Expr, ExternDef, FStringPart,
    FunctionDef, IfStmt, LambdaParam, MacroArg, MacroBody, MacroDef, MacroParam, MatchStmt, Node,
    Pattern, PointerKind, RangeBound, Type, UnaryOp, UnitDef, WithStmt,
};
use tracing::instrument;

use crate::effects::{check_async_violation, CURRENT_EFFECT};
use crate::error::CompileError;
use crate::value::{
    BorrowMutValue, BorrowValue, ChannelValue, Env, FutureValue, GeneratorValue, ManualHandleValue,
    ManualSharedValue, ManualUniqueValue, ManualWeakValue, OptionVariant, ResultVariant,
    SpecialEnumType, ThreadPoolValue, Value, ATTR_STRONG, BUILTIN_ARRAY, BUILTIN_CHANNEL,
    BUILTIN_RANGE, METHOD_MISSING, METHOD_NEW, METHOD_SELF,
};

//==============================================================================
// Execution Context (for formal verification)
//==============================================================================
// This enum models the interpreter's execution mode as an explicit state machine.
// Each variant represents a distinct execution context with its own requirements.
//
// Lean equivalent:
// ```lean
// inductive ExecutionMode
//   | normal                                         -- Regular function execution
//   | actor (inbox : Receiver) (outbox : Sender)    -- Actor message loop
//   | generator (yields : List Value)                -- Generator with accumulated yields
//   | context (obj : Value)                          -- DSL context block
// ```

/// Execution mode for the interpreter
///
/// Models the current execution context as a state machine.
/// Invalid state combinations are unrepresentable.
#[derive(Debug, Clone)]
pub enum ExecutionMode {
    /// Normal function execution (no special context)
    Normal,
    /// Actor execution with message channels
    Actor {
        inbox: Arc<Mutex<mpsc::Receiver<Message>>>,
        outbox: mpsc::Sender<Message>,
    },
    /// Generator execution accumulating yield values
    Generator { yields: Vec<Value> },
    /// Context block with DSL object
    Context { object: Value },
}

impl ExecutionMode {
    /// Check if running in actor mode
    pub fn is_actor(&self) -> bool {
        matches!(self, ExecutionMode::Actor { .. })
    }

    /// Check if running in generator mode
    pub fn is_generator(&self) -> bool {
        matches!(self, ExecutionMode::Generator { .. })
    }

    /// Check if running in context mode
    pub fn is_context(&self) -> bool {
        matches!(self, ExecutionMode::Context { .. })
    }

    /// Get actor inbox if in actor mode
    pub fn actor_inbox(&self) -> Option<&Arc<Mutex<mpsc::Receiver<Message>>>> {
        match self {
            ExecutionMode::Actor { inbox, .. } => Some(inbox),
            _ => None,
        }
    }

    /// Get actor outbox if in actor mode
    pub fn actor_outbox(&self) -> Option<&mpsc::Sender<Message>> {
        match self {
            ExecutionMode::Actor { outbox, .. } => Some(outbox),
            _ => None,
        }
    }

    /// Get mutable yields if in generator mode
    pub fn generator_yields_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            ExecutionMode::Generator { yields } => Some(yields),
            _ => None,
        }
    }

    /// Take yields from generator mode, returning empty vec if not generator
    pub fn take_generator_yields(&mut self) -> Vec<Value> {
        match self {
            ExecutionMode::Generator { yields } => std::mem::take(yields),
            _ => Vec::new(),
        }
    }

    /// Get context object if in context mode
    pub fn context_object(&self) -> Option<&Value> {
        match self {
            ExecutionMode::Context { object } => Some(object),
            _ => None,
        }
    }
}

// Thread-local state for interpreter execution
// Note: EXECUTION_MODE provides type-safe state; legacy fields kept for compatibility
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
    /// Type-safe execution mode (new, replaces Option fields above)
    pub(crate) static EXECUTION_MODE: RefCell<ExecutionMode> = RefCell::new(ExecutionMode::Normal);
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

/// Stores unit family definitions: family_name -> (base_type, variants with factors)
/// Used for to_X() conversion methods between related units
pub(crate) type UnitFamilies = HashMap<String, UnitFamilyInfo>;

/// Information about a unit family for conversion support
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields used when to_X() method dispatch is implemented
pub(crate) struct UnitFamilyInfo {
    /// Base type (e.g., f64)
    pub base_type: Type,
    /// Map of suffix -> conversion factor to base unit
    pub conversions: HashMap<String, f64>,
}

/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(Value),
    #[allow(dead_code)]
    Break(Option<Value>),
    Continue,
}

/// Call a value (function or lambda) with evaluated arguments.
/// Used for decorator application where we have Value arguments, not AST Arguments.
fn call_value_with_args(
    callee: &Value,
    args: Vec<Value>,
    _env: &Env,
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
            control_to_value(result)
        }
        _ => Err(CompileError::Semantic(format!(
            "cannot call value of type {}",
            callee.type_name()
        ))),
    }
}

/// Built-in extern functions that are always available without explicit declaration.
/// These are the "prelude" functions - print, math, and conversion utilities.
pub const PRELUDE_EXTERN_FUNCTIONS: &[&str] = &[
    // I/O functions
    "print",
    "println",
    "eprint",
    "eprintln",
    "input",
    // Math functions
    "abs",
    "min",
    "max",
    "sqrt",
    "floor",
    "ceil",
    "pow",
    // Conversion functions
    "to_string",
    "to_int",
    // Process control
    "exit",
];

/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    // Clear const names and extern functions from previous runs
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    EXTERN_FUNCTIONS.with(|cell| {
        let mut externs = cell.borrow_mut();
        externs.clear();
        // Pre-populate with prelude functions (always available)
        for &name in PRELUDE_EXTERN_FUNCTIONS {
            externs.insert(name.to_string());
        }
    });

    let mut env = Env::new();
    let mut functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut classes: HashMap<String, ClassDef> = HashMap::new();
    let mut enums: Enums = HashMap::new();
    let mut impl_methods: ImplMethods = HashMap::new();
    let mut extern_functions: ExternFunctions = HashMap::new();
    let mut macros: Macros = HashMap::new();
    let mut units: Units = HashMap::new();
    let mut unit_families: UnitFamilies = HashMap::new();

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
                // Register struct as a constructor-like callable
                // Store in env as Constructor value so it can be called like Point(x, y)
                env.insert(s.name.clone(), Value::Constructor { class_name: s.name.clone() });
                // Also register as a class so instantiation works
                classes.insert(
                    s.name.clone(),
                    ClassDef {
                        span: s.span,
                        name: s.name.clone(),
                        generic_params: Vec::new(),
                        fields: s.fields.clone(),
                        methods: Vec::new(),
                        parent: None,
                        visibility: s.visibility,
                        attributes: Vec::new(),
                    },
                );
            }
            Node::Enum(e) => {
                enums.insert(e.name.clone(), e.clone());
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                // Store in env as Constructor value so it can be called like MyClass()
                env.insert(c.name.clone(), Value::Constructor { class_name: c.name.clone() });
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
            Node::UnitFamily(uf) => {
                // Unit family defines multiple related units with conversion factors
                // Register each variant as a standalone unit
                let mut conversions = HashMap::new();
                for variant in &uf.variants {
                    // Create a synthetic UnitDef for each variant
                    // Unit families have a single base type
                    let unit_def = UnitDef {
                        span: uf.span,
                        name: format!("{}_{}", uf.name, variant.suffix),
                        base_types: vec![uf.base_type.clone()],
                        suffix: variant.suffix.clone(),
                        visibility: uf.visibility,
                    };
                    units.insert(variant.suffix.clone(), unit_def);
                    // Store conversion factor for to_X() methods
                    conversions.insert(variant.suffix.clone(), variant.factor);
                }
                // Store the family with all conversion factors
                unit_families.insert(
                    uf.name.clone(),
                    UnitFamilyInfo {
                        base_type: uf.base_type.clone(),
                        conversions,
                    },
                );
                // Store the family name for reference
                env.insert(uf.name.clone(), Value::Nil);
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
                if let Expr::FunctionalUpdate { target, method, args } = expr {
                    if let Some((name, new_value)) = handle_functional_update(
                        target, method, args, &env, &functions, &classes, &enums, &impl_methods
                    )? {
                        env.insert(name, new_value);
                        continue;
                    }
                }
                // Handle method calls on objects - need to persist mutations to self
                let (_, update) = handle_method_call_with_self_update(
                    expr, &env, &functions, &classes, &enums, &impl_methods
                )?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }
            }
            Node::Break(_) => {
                return Err(CompileError::Semantic("break outside of loop".into()));
            }
            Node::Continue(_) => {
                return Err(CompileError::Semantic("continue outside of loop".into()));
            }
            // Module system nodes - parsed but not interpreted at this level
            // Module resolution happens before interpretation
            Node::ModDecl(_)
            | Node::UseStmt(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::AutoImportStmt(_) => {
                // Module system is handled by the module resolver
                // These are no-ops in the interpreter
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
                // Handle method calls on objects - need to persist mutations to self
                let (value, update) = handle_method_call_with_self_update(
                    value_expr, env, functions, classes, enums, impl_methods
                )?;
                if let Some((obj_name, new_self)) = update {
                    env.insert(obj_name, new_self);
                }
                let is_mutable = let_stmt.mutability.is_mutable();
                match &let_stmt.pattern {
                    Pattern::Identifier(_) | Pattern::MutIdentifier(_) => {
                        bind_let_pattern_element(&let_stmt.pattern, value, is_mutable, env);
                    }
                    Pattern::Tuple(patterns) => {
                        // Allow tuple pattern to match both Tuple and Array
                        let values: Vec<Value> = match value {
                            Value::Tuple(v) => v,
                            Value::Array(v) => v,
                            _ => Vec::new(),
                        };
                        bind_collection_pattern(patterns, values, is_mutable, env);
                    }
                    Pattern::Array(patterns) => {
                        if let Value::Array(values) = value {
                            bind_collection_pattern(patterns, values, is_mutable, env);
                        }
                    }
                    _ => {}
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
                // Handle method calls on objects - need to persist mutations to self
                let (value, update) = handle_method_call_with_self_update(
                    &assign.value, env, functions, classes, enums, impl_methods
                )?;
                if let Some((obj_name, new_self)) = update {
                    env.insert(obj_name, new_self);
                }
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
            } else if let Expr::Tuple(targets) = &assign.target {
                // Handle tuple unpacking: (a, b) = (x, y)
                let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                let values: Vec<Value> = match value {
                    Value::Tuple(v) => v,
                    Value::Array(v) => v,
                    _ => return Err(CompileError::Semantic("tuple unpacking requires tuple or array on right side".into())),
                };
                if targets.len() != values.len() {
                    return Err(CompileError::Semantic(format!(
                        "tuple unpacking length mismatch: expected {}, got {}",
                        targets.len(), values.len()
                    )));
                }
                for (target_expr, val) in targets.iter().zip(values.into_iter()) {
                    if let Expr::Identifier(name) = target_expr {
                        env.insert(name.clone(), val);
                    } else {
                        return Err(CompileError::Semantic("tuple unpacking target must be identifier".into()));
                    }
                }
                Ok(Control::Next)
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
            if let Expr::FunctionalUpdate { target, method, args } = expr {
                if let Some((name, new_value)) = handle_functional_update(
                    target, method, args, env, functions, classes, enums, impl_methods
                )? {
                    env.insert(name, new_value);
                    return Ok(Control::Next);
                }
            }
            // Handle method calls on objects - need to persist mutations to self
            let (_, update) = handle_method_call_with_self_update(
                expr, env, functions, classes, enums, impl_methods
            )?;
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

/// Helper to execute a method function with self context (for auto-forwarding properties)
fn exec_method_function(
    method: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    self_val: &Value,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Object { class, fields } = self_val {
        exec_function(method, args, env, functions, classes, enums, impl_methods, Some((class.as_str(), fields)))
    } else {
        Err(CompileError::Semantic("exec_method_function called with non-object self".into()))
    }
}

// Expression evaluation (extracted for maintainability)
include!("interpreter_expr.rs");

// Include helper functions (method dispatch, array/dict ops, pattern binding, slicing)
include!("interpreter_helpers.rs");

// Include the rest of the interpreter functions
include!("interpreter_call.rs");
include!("interpreter_method.rs");
include!("interpreter_macro.rs");
include!("interpreter_extern.rs");
include!("interpreter_context.rs");
