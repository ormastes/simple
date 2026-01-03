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
use std::collections::{HashMap, HashSet};
use std::sync::atomic::AtomicBool;
use std::sync::{mpsc, Arc, Mutex};

use simple_common::actor::{ActorSpawner, Message, ThreadSpawner};
use simple_parser::ast::{
    AssignOp, AssignmentStmt, BinOp, BinaryArithmeticOp, Block, ClassDef, ContextStmt, EnumDef,
    Expr, ExternDef, FStringPart, ForStmt, FunctionDef, IfStmt, LambdaParam, LetStmt, LoopStmt,
    MacroArg, MacroContractItem, MacroDef, MacroStmt, MatchArm, MatchStmt, Node, Pattern,
    PointerKind, RangeBound, ReturnStmt, Type, UnaryArithmeticOp, UnaryOp, UnitDef, WhileStmt,
    WithStmt, ImplBlock,
};
use tracing::instrument;

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::effects::check_effect_violations;
use crate::error::CompileError;
use crate::value::{
    BorrowMutValue, BorrowValue, ChannelValue, Env, FutureValue, GeneratorValue, ManualHandleValue,
    ManualSharedValue, ManualUniqueValue, ManualWeakValue, OptionVariant, ResultVariant,
    SpecialEnumType, ThreadPoolValue, Value, ATTR_STRONG, BUILTIN_ARRAY, BUILTIN_CHANNEL,
    BUILTIN_RANGE, METHOD_MISSING, METHOD_NEW, METHOD_SELF,
};

// Unit system support (SI prefixes, dimensional analysis, constraints)
pub(crate) use crate::interpreter_unit::*;

thread_local! {
    pub(crate) static DI_CONFIG: RefCell<Option<Arc<DiConfig>>> = RefCell::new(None);
    pub(crate) static DI_SINGLETONS: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
    pub(crate) static AOP_CONFIG: RefCell<Option<Arc<AopConfig>>> = RefCell::new(None);
    /// Command line arguments passed to the Simple interpreter
    pub(crate) static INTERPRETER_ARGS: RefCell<Vec<String>> = RefCell::new(Vec::new());
}

/// Global interrupt flag for Ctrl-C handling.
///
/// This flag is set to true when the user presses Ctrl-C, signaling that
/// execution should stop gracefully. The interpreter checks this flag
/// at loop iterations and other long-running operations.
///
/// Thread-safe via atomic operations with SeqCst ordering for signal handlers.
pub(crate) static INTERRUPT_REQUESTED: AtomicBool = AtomicBool::new(false);

/// Initialize signal handlers for Ctrl-C.
///
/// This function should be called once at program startup to install
/// a handler that sets the INTERRUPT_REQUESTED flag when Ctrl-C is pressed.
///
/// # Example
///
/// ```ignore
/// simple_compiler::interpreter::init_signal_handlers();
/// ```
pub fn init_signal_handlers() {
    use std::sync::atomic::Ordering;

    let result = ctrlc::set_handler(move || {
        eprintln!("\n^C Interrupt received - stopping execution...");
        INTERRUPT_REQUESTED.store(true, Ordering::SeqCst);
    });

    if let Err(e) = result {
        tracing::warn!(error = %e, "Failed to install Ctrl-C handler");
    }
}

/// Check if user requested interrupt (Ctrl-C).
///
/// Returns true if the INTERRUPT_REQUESTED flag is set.
/// Uses Relaxed ordering for performance - this is safe because
/// we only need eventual visibility, not strict ordering.
#[inline]
pub fn is_interrupted() -> bool {
    INTERRUPT_REQUESTED.load(std::sync::atomic::Ordering::Relaxed)
}

/// Reset interrupt flag (for REPL mode).
///
/// Clears the INTERRUPT_REQUESTED flag to allow new commands to run
/// after a previous command was interrupted.
pub fn reset_interrupt() {
    INTERRUPT_REQUESTED.store(false, std::sync::atomic::Ordering::SeqCst);
}

pub(crate) fn set_di_config(di: Option<DiConfig>) {
    DI_CONFIG.with(|cell| {
        *cell.borrow_mut() = di.map(Arc::new);
    });
    DI_SINGLETONS.with(|cell| cell.borrow_mut().clear());
}

pub(crate) fn get_di_config() -> Option<Arc<DiConfig>> {
    DI_CONFIG.with(|cell| cell.borrow().clone())
}

pub(crate) fn set_aop_config(config: Option<AopConfig>) {
    AOP_CONFIG.with(|cell| {
        *cell.borrow_mut() = config.map(Arc::new);
    });
}

pub(crate) fn get_aop_config() -> Option<Arc<AopConfig>> {
    AOP_CONFIG.with(|cell| cell.borrow().clone())
}

/// Set the command line arguments for the interpreter
pub fn set_interpreter_args(args: Vec<String>) {
    INTERPRETER_ARGS.with(|cell| {
        *cell.borrow_mut() = args;
    });
}

/// Get the command line arguments passed to the interpreter
pub fn get_interpreter_args() -> Vec<String> {
    INTERPRETER_ARGS.with(|cell| cell.borrow().clone())
}

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
    /// Name of the variable holding the context object (for mutation persistence)
    pub(crate) static CONTEXT_VAR_NAME: RefCell<Option<String>> = RefCell::new(None);
    /// Accumulated yield values during generator execution
    pub(crate) static GENERATOR_YIELDS: RefCell<Option<Vec<Value>>> = RefCell::new(None);
    /// User-defined macros
    pub(crate) static USER_MACROS: RefCell<HashMap<String, MacroDef>> = RefCell::new(HashMap::new());
    /// Order in which macros are defined (for validating defined-before-use)
    pub(crate) static MACRO_DEFINITION_ORDER: RefCell<Vec<String>> = RefCell::new(Vec::new());
    /// Type-safe execution mode (new, replaces Option fields above)
    pub(crate) static EXECUTION_MODE: RefCell<ExecutionMode> = RefCell::new(ExecutionMode::Normal);
    /// Maps unit suffix -> family name (for looking up which family a unit belongs to)
    pub(crate) static UNIT_SUFFIX_TO_FAMILY: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
    /// Maps family_name -> (suffix -> conversion_factor) for unit conversions
    pub(crate) static UNIT_FAMILY_CONVERSIONS: RefCell<HashMap<String, HashMap<String, f64>>> = RefCell::new(HashMap::new());
    /// Maps family_name -> UnitArithmeticRules for type-safe arithmetic checking
    pub(crate) static UNIT_FAMILY_ARITHMETIC: RefCell<HashMap<String, UnitArithmeticRules>> = RefCell::new(HashMap::new());
    /// Maps compound_unit_name -> Dimension (for dimensional analysis)
    pub(crate) static COMPOUND_UNIT_DIMENSIONS: RefCell<HashMap<String, Dimension>> = RefCell::new(HashMap::new());
    /// Maps base_family_name -> Dimension (for base unit families like length, time)
    pub(crate) static BASE_UNIT_DIMENSIONS: RefCell<HashMap<String, Dimension>> = RefCell::new(HashMap::new());
    /// Maps base unit suffix -> family name for SI prefix detection (e.g., "m" -> "length")
    pub(crate) static SI_BASE_UNITS: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
    /// Tracks variables that have been moved (for unique pointer move semantics)
    /// When a unique pointer is used (moved out), its name is added here.
    /// Any subsequent access to a moved variable results in a compile error.
    pub(crate) static MOVED_VARS: RefCell<std::collections::HashSet<String>> = RefCell::new(std::collections::HashSet::new());
    /// Module-level mutable variables accessible from functions.
    /// When a module declares `let mut x = ...` at top level, x is added here.
    /// Functions can read and write these variables.
    pub(crate) static MODULE_GLOBALS: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
}

/// Mark a variable as moved (for unique pointer move semantics).
/// Called when a unique pointer is assigned to another variable.
pub(crate) fn mark_as_moved(name: &str) {
    MOVED_VARS.with(|cell| {
        cell.borrow_mut().insert(name.to_string());
    });
}

/// Clear moved variables tracking (for new scopes/functions).
pub(crate) fn clear_moved_vars() {
    MOVED_VARS.with(|cell| {
        cell.borrow_mut().clear();
    });
}

/// Check if an expression is a simple identifier (for move tracking)
fn get_identifier_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Identifier(name) => Some(name.as_str()),
        _ => None,
    }
}

/// Extract the variable name from a pattern (for module-level global tracking)
fn get_pattern_name(pattern: &simple_parser::ast::Pattern) -> Option<String> {
    match pattern {
        simple_parser::ast::Pattern::Identifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::MutIdentifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::Typed { pattern, .. } => get_pattern_name(pattern),
        _ => None,
    }
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

/// Stores trait definitions: trait_name -> TraitDef
pub(crate) type Traits = HashMap<String, simple_parser::ast::TraitDef>;

/// Stores trait implementations: (trait_name, type_name) -> list of methods
/// Used to track which types implement which traits
pub(crate) type TraitImpls = HashMap<(String, String), Vec<FunctionDef>>;


/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(Value),
    #[allow(dead_code)]
    Break(Option<Value>),
    Continue,
}


/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, None, None)
}

pub fn evaluate_module_with_di(
    items: &[Node],
    di_config: Option<&DiConfig>,
) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, di_config, None)
}

pub fn evaluate_module_with_di_and_aop(
    items: &[Node],
    di_config: Option<&DiConfig>,
    aop_config: Option<&AopConfig>,
) -> Result<i32, CompileError> {
    set_di_config(di_config.cloned());
    set_aop_config(aop_config.cloned());
    let result = interpreter_eval::evaluate_module_impl(items);
    set_di_config(None);
    set_aop_config(None);
    result
}


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
                let (value, update) = handle_method_call_with_self_update(
                    value_expr,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
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
                        simple_parser::ast::Pattern::Typed { pattern, .. } => {
                            match pattern.as_ref() {
                                simple_parser::ast::Pattern::Identifier(name) => name.clone(),
                                simple_parser::ast::Pattern::MutIdentifier(name) => name.clone(),
                                _ => "<pattern>".to_string(),
                            }
                        }
                        _ => "<pattern>".to_string(),
                    }
                };

                // Validate and constrain value based on type annotation
                let value = match &type_annotation {
                    Some(Type::Simple(type_name)) if is_unit_type(type_name) => {
                        if let Err(e) = validate_unit_type(&value, type_name) {
                            let var_name = get_var_name(&let_stmt.pattern);
                            return Err(CompileError::Semantic(format!("let binding '{}': {}", var_name, e)));
                        }
                        value
                    }
                    Some(Type::UnitWithRepr { name, constraints, .. }) => {
                        // Validate and apply unit type constraints (range, overflow behavior)
                        match validate_unit_constraints(value, name, constraints) {
                            Ok(constrained_value) => constrained_value,
                            Err(e) => {
                                let var_name = get_var_name(&let_stmt.pattern);
                                return Err(CompileError::Semantic(format!("let binding '{}': {}", var_name, e)));
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
                    &assign.value,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
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
                        // Collect all known names for typo suggestion
                        let known_names: Vec<&str> = env
                            .keys()
                            .map(|s| s.as_str())
                            .chain(functions.keys().map(|s| s.as_str()))
                            .chain(classes.keys().map(|s| s.as_str()))
                            .collect();
                        let mut msg = format!("undefined variable '{obj_name}'");
                        if let Some(suggestion) =
                            crate::error::typo::format_suggestion(obj_name, known_names)
                        {
                            msg.push_str(&format!("; {}", suggestion));
                        }
                        Err(CompileError::Semantic(msg))
                    }
                } else {
                    Err(CompileError::Semantic(
                        "field assignment requires identifier as object".into(),
                    ))
                }
            } else if let Expr::Tuple(targets) = &assign.target {
                // Handle tuple unpacking: (a, b) = (x, y)
                let value =
                    evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                let values: Vec<Value> = match value {
                    Value::Tuple(v) => v,
                    Value::Array(v) => v,
                    _ => {
                        return Err(CompileError::Semantic(
                            "tuple unpacking requires tuple or array on right side".into(),
                        ))
                    }
                };
                if targets.len() != values.len() {
                    return Err(CompileError::Semantic(format!(
                        "tuple unpacking length mismatch: expected {}, got {}",
                        targets.len(),
                        values.len()
                    )));
                }
                for (target_expr, val) in targets.iter().zip(values.into_iter()) {
                    if let Expr::Identifier(name) = target_expr {
                        env.insert(name.clone(), val);
                    } else {
                        return Err(CompileError::Semantic(
                            "tuple unpacking target must be identifier".into(),
                        ));
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
            if let Expr::FunctionalUpdate {
                target,
                method,
                args,
            } = expr
            {
                if let Some((name, new_value)) = handle_functional_update(
                    target,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )? {
                    env.insert(name, new_value);
                    return Ok(Control::Next);
                }
            }
            // Handle method calls on objects - need to persist mutations to self
            let (_, update) = handle_method_call_with_self_update(
                expr,
                env,
                functions,
                classes,
                enums,
                impl_methods,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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

/// Execute a block in a function context, supporting implicit return.
/// If the last statement is an expression, its value is captured and returned.
pub(crate) fn exec_block_fn(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    let len = block.statements.len();
    let mut last_expr_value: Option<Value> = None;

    for (i, stmt) in block.statements.iter().enumerate() {
        // For the last statement, if it's an expression, capture its value
        let is_last = i == len - 1;
        if is_last {
            if let Node::Expression(expr) = stmt {
                // Evaluate and capture the value for implicit return
                let val = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
                last_expr_value = Some(val);
                continue;
            }
        }

        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => {
                return Ok((flow, None));
            }
        }
    }
    Ok((Control::Next, last_expr_value))
}

//==============================================================================
// Error handling macros to reduce boilerplate
//==============================================================================

// These macros are defined for potential future use
#[allow(unused_macros)]
/// Create a runtime error with message
macro_rules! runtime_err {
    ($msg:expr) => {
        crate::error::CompileError::Runtime($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Runtime(format!($fmt, $($arg)*))
    };
}

/// Create a semantic error with message
macro_rules! semantic_err {
    ($msg:expr) => {
        crate::error::CompileError::Semantic($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Semantic(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)]
/// Create a codegen error with message
macro_rules! codegen_err {
    ($msg:expr) => {
        crate::error::CompileError::Codegen($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Codegen(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)]
/// Return early with a runtime error
macro_rules! bail_runtime {
    ($msg:expr) => {
        return Err(runtime_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(runtime_err!($fmt, $($arg)*))
    };
}

/// Return early with a semantic error
macro_rules! bail_semantic {
    ($msg:expr) => {
        return Err(semantic_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(semantic_err!($fmt, $($arg)*))
    };
}

/// Return early with unknown method error (with typo suggestions)
macro_rules! bail_unknown_method {
    ($method:expr, $type_name:expr, $available:expr) => {{
        let mut msg = format!("unknown method {} on {}", $method, $type_name);
        if let Some(suggestion) = crate::error::typo::format_suggestion($method, $available.iter().copied()) {
            msg.push_str(&format!("; {}", suggestion));
        }
        return Err(semantic_err!("{}", msg));
    }};
}

// Control flow functions (if, while, loop, for, match, pattern_matches)
#[path = "interpreter_control.rs"]
mod interpreter_control;
use interpreter_control::{
    check_enum_exhaustiveness, collect_covered_variants, exec_context, exec_for, exec_if,
    exec_loop, exec_match, exec_while, exec_with, is_catch_all_pattern, pattern_matches,
};

/// Helper to execute a method function with self context (for auto-forwarding properties)
fn exec_method_function(
    method: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    self_val: &Value,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Object { class, fields } = self_val {
        exec_function(
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            Some((class.as_str(), fields)),
        )
    } else {
        Err(CompileError::Semantic(
            "exec_method_function called with non-object self".into(),
        ))
    }
}

include!("interpreter_expr.rs");

// Helper functions (method dispatch, array/dict ops, pattern binding, slicing)
#[path = "interpreter_helpers.rs"]
mod interpreter_helpers;
pub(crate) use interpreter_helpers::{
    bind_pattern, bind_pattern_value, comprehension_iterate, control_to_value, create_range_object,
    eval_arg, eval_arg_int, eval_arg_usize, eval_array_all, eval_array_any, eval_array_filter,
    eval_array_find, eval_array_map, eval_array_reduce, eval_dict_filter, eval_dict_map_values,
    eval_option_and_then, eval_option_filter, eval_option_map, eval_option_or_else,
    eval_result_and_then, eval_result_map, eval_result_map_err, eval_result_or_else,
    find_and_exec_method, handle_functional_update, handle_method_call_with_self_update,
    iter_to_vec, message_to_value, normalize_index, slice_collection, spawn_actor_with_expr,
    spawn_future_with_callable, spawn_future_with_callable_and_env, spawn_future_with_expr,
    try_method_missing, with_effect_context,
};

// Include the rest of the interpreter functions
#[path = "interpreter_call/mod.rs"]
mod interpreter_call;
use interpreter_call::{evaluate_call, BDD_INDENT, BDD_COUNTS, BDD_SHARED_EXAMPLES,
                       BDD_CONTEXT_DEFS, BDD_BEFORE_EACH, BDD_AFTER_EACH, BDD_LAZY_VALUES,
                       exec_function, exec_function_with_values, exec_function_with_captured_env,
                       bind_args, bind_args_with_injected, exec_lambda, instantiate_class,
                       exec_block_value};

// Module loading and resolution
#[path = "interpreter_module.rs"]
mod interpreter_module;
use interpreter_module::{
    evaluate_module_exports, get_import_alias, load_and_merge_module, merge_module_definitions,
    resolve_module_path,
};

// Type-related utilities
#[path = "interpreter_types.rs"]
mod interpreter_types;
use interpreter_types::{get_type_name, register_trait_impl, TraitImplRegistry};

// Core module evaluation logic
#[path = "interpreter_eval.rs"]
mod interpreter_eval;

#[path = "interpreter_method/mod.rs"]
mod interpreter_method;
use interpreter_method::{evaluate_method_call, evaluate_method_call_with_self_update};
include!("interpreter_macro.rs");
#[path = "interpreter_native_io.rs"]
mod interpreter_native_io;
// Re-export all native I/O functions
pub use interpreter_native_io::*;
#[path = "interpreter_native_net.rs"]
mod interpreter_native_net;
// Re-export all native networking functions
pub use interpreter_native_net::*;
#[path = "interpreter_context.rs"]
mod interpreter_context;
use interpreter_context::dispatch_context_method;
#[path = "interpreter_extern.rs"]
mod interpreter_extern;
pub(crate) use interpreter_extern::call_extern_function;
