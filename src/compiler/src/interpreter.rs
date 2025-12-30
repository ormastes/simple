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

#[derive(Default)]
struct TraitImplRegistry {
    blanket_impl: bool,
    default_blanket_impl: bool,
    specific_impls: HashSet<String>,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    let result = evaluate_module_impl(items);
    set_di_config(None);
    set_aop_config(None);
    result
}

fn evaluate_module_impl(items: &[Node]) -> Result<i32, CompileError> {
    // Clear const names, extern functions, and moved variables from previous runs
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    clear_moved_vars();
    EXTERN_FUNCTIONS.with(|cell| {
        let mut externs = cell.borrow_mut();
        externs.clear();
        // Pre-populate with prelude functions (always available)
        for &name in PRELUDE_EXTERN_FUNCTIONS {
            externs.insert(name.to_string());
        }
    });
    // Clear macro definition order from previous runs
    MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().clear());
    // Clear unit family info from previous runs
    UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_CONVERSIONS.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_ARITHMETIC.with(|cell| cell.borrow_mut().clear());
    COMPOUND_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    BASE_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    SI_BASE_UNITS.with(|cell| cell.borrow_mut().clear());
    // Clear module-level globals from previous runs
    MODULE_GLOBALS.with(|cell| cell.borrow_mut().clear());

    let mut env = Env::new();
    let mut functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut classes: HashMap<String, ClassDef> = HashMap::new();
    let mut enums: Enums = HashMap::new();
    let mut impl_methods: ImplMethods = HashMap::new();
    let mut extern_functions: ExternFunctions = HashMap::new();
    let mut macros: Macros = HashMap::new();
    let mut units: Units = HashMap::new();
    let mut unit_families: UnitFamilies = HashMap::new();
    let mut traits: Traits = HashMap::new();
    let mut trait_impls: TraitImpls = HashMap::new();
    let mut trait_impl_registry: HashMap<String, TraitImplRegistry> = HashMap::new();

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
                            &mut functions,
                            &mut classes,
                            &enums,
                            &impl_methods,
                        )?;

                        // If decorator has arguments, call it first to get the actual decorator
                        let actual_decorator = if let Some(args) = &decorator.args {
                            let mut arg_values = vec![];
                            for arg in args {
                                arg_values.push(evaluate_expr(
                                    &arg.value,
                                    &env,
                                    &mut functions,
                                    &mut classes,
                                    &enums,
                                    &impl_methods,
                                )?);
                            }
                            call_value_with_args(
                                &decorator_fn,
                                arg_values,
                                &env,
                                &mut functions,
                                &mut classes,
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
                            &mut functions,
                            &mut classes,
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
                env.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
                // Also register as a class so instantiation works
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
                        attributes: Vec::new(),
                        doc_comment: None,
                        invariant: None,
                    },
                );
            }
            Node::Enum(e) => {
                enums.insert(e.name.clone(), e.clone());
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                // Store in env as Constructor value so it can be called like MyClass()
                env.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                register_trait_impl(&mut trait_impl_registry, impl_block)?;
                let type_name = get_type_name(&impl_block.target_type);
                let methods = impl_methods.entry(type_name.clone()).or_insert_with(Vec::new);
                for method in &impl_block.methods {
                    methods.push(method.clone());
                }

                // If this is a trait implementation, verify and register it
                if let Some(ref trait_name) = impl_block.trait_name {
                    // Verify trait exists
                    if let Some(trait_def) = traits.get(trait_name) {
                        // Check all abstract trait methods are implemented
                        let impl_method_names: std::collections::HashSet<_> = impl_block
                            .methods
                            .iter()
                            .map(|m| m.name.clone())
                            .collect();

                        for trait_method in &trait_def.methods {
                            // Only require implementation of abstract methods
                            if trait_method.is_abstract
                                && !impl_method_names.contains(&trait_method.name)
                            {
                                return Err(CompileError::Semantic(format!(
                                    "type `{}` does not implement required method `{}` from trait `{}`",
                                    type_name, trait_method.name, trait_name
                                )));
                            }
                        }

                        // Build combined methods: impl methods + default trait methods
                        let mut combined_methods = impl_block.methods.clone();
                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract
                                && !impl_method_names.contains(&trait_method.name)
                            {
                                combined_methods.push(trait_method.clone());
                                // Also add to impl_methods so method dispatch can find it
                                methods.push(trait_method.clone());
                            }
                        }

                        // Store the trait implementation with combined methods
                        trait_impls.insert(
                            (trait_name.clone(), type_name.clone()),
                            combined_methods,
                        );
                    }
                    // Note: If trait not found, it might be defined in another module
                    // For now, we silently allow this for forward compatibility
                }
            }
            Node::Extern(ext) => {
                extern_functions.insert(ext.name.clone(), ext.clone());
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::Macro(m) => {
                macros.insert(m.name.clone(), m.clone());
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));

                // Track macro definition order for one-pass LL(1) validation (#1304)
                MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().push(m.name.clone()));

                // Process macro contracts to register introduced symbols (#1303)
                // Note: For now, contracts with const params need invocation-time processing
                // But we can process non-parameterized contracts at definition time
                // TODO: Full integration requires invocation-time symbol registration
            }
            Node::Trait(t) => {
                // Register trait definition for use in impl checking
                traits.insert(t.name.clone(), t.clone());
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
                        where_clause: vec![],
                        fields: a.fields.clone(),
                        methods: a.methods.clone(),
                        parent: None,
                        visibility: a.visibility,
                        attributes: vec![],
                        doc_comment: None,
                        invariant: None,
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
                    // Register suffix -> family mapping in thread-local for expression evaluation
                    UNIT_SUFFIX_TO_FAMILY.with(|cell| {
                        cell.borrow_mut().insert(variant.suffix.clone(), uf.name.clone());
                    });
                }
                // Store the family with all conversion factors
                unit_families.insert(
                    uf.name.clone(),
                    UnitFamilyInfo {
                        base_type: uf.base_type.clone(),
                        conversions: conversions.clone(),
                    },
                );
                // Register family conversions in thread-local for method dispatch
                UNIT_FAMILY_CONVERSIONS.with(|cell| {
                    cell.borrow_mut().insert(uf.name.clone(), conversions);
                });
                // Store arithmetic rules if present
                if let Some(arith) = &uf.arithmetic {
                    let rules = UnitArithmeticRules {
                        binary_rules: arith.binary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.operand_type), type_to_family_name(&r.result_type))
                        }).collect(),
                        unary_rules: arith.unary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.result_type))
                        }).collect(),
                    };
                    UNIT_FAMILY_ARITHMETIC.with(|cell| {
                        cell.borrow_mut().insert(uf.name.clone(), rules);
                    });
                }
                // Store the family name for reference
                env.insert(uf.name.clone(), Value::Nil);
                // Register this as a base dimension (self-referential)
                // e.g., "length" has dimension {length: 1}
                BASE_UNIT_DIMENSIONS.with(|cell| {
                    cell.borrow_mut().insert(uf.name.clone(), Dimension::base(&uf.name));
                });
                // Register the base unit (factor = 1.0) for SI prefix support
                // e.g., for length: "m" -> "length", so "km" can be parsed as "k" + "m"
                for variant in &uf.variants {
                    if (variant.factor - 1.0).abs() < f64::EPSILON {
                        SI_BASE_UNITS.with(|cell| {
                            cell.borrow_mut().insert(variant.suffix.clone(), uf.name.clone());
                        });
                        break; // Only one base unit per family
                    }
                }
            }
            Node::CompoundUnit(cu) => {
                // Compound unit defines a derived unit (e.g., velocity = length / time)
                // Register the compound unit name in the environment
                env.insert(cu.name.clone(), Value::Nil);
                // Store arithmetic rules if present
                if let Some(arith) = &cu.arithmetic {
                    let rules = UnitArithmeticRules {
                        binary_rules: arith.binary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.operand_type), type_to_family_name(&r.result_type))
                        }).collect(),
                        unary_rules: arith.unary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.result_type))
                        }).collect(),
                    };
                    UNIT_FAMILY_ARITHMETIC.with(|cell| {
                        cell.borrow_mut().insert(cu.name.clone(), rules);
                    });
                }
                // Convert the UnitExpr to a Dimension and store it
                let dimension = Dimension::from_unit_expr(&cu.expr);
                COMPOUND_UNIT_DIMENSIONS.with(|cell| {
                    cell.borrow_mut().insert(cu.name.clone(), dimension);
                });
            }
            Node::Let(let_stmt) => {
                if let Control::Return(val) =
                    exec_node(item, &mut env, &mut functions, &mut classes, &enums, &impl_methods)?
                {
                    return val.as_int().map(|v| v as i32);
                }
                // Sync mutable module-level variables to MODULE_GLOBALS for function access
                if let_stmt.mutability.is_mutable() {
                    if let Some(name) = get_pattern_name(&let_stmt.pattern) {
                        if let Some(value) = env.get(&name) {
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut().insert(name, value.clone());
                            });
                        }
                    }
                }
            }
            Node::Const(_)
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
                    exec_node(item, &mut env, &mut functions, &mut classes, &enums, &impl_methods)?
                {
                    return val.as_int().map(|v| v as i32);
                }
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let val =
                        evaluate_expr(expr, &env, &mut functions, &mut classes, &enums, &impl_methods)?;
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
                    if let Some((name, new_value)) = handle_functional_update(
                        target,
                        method,
                        args,
                        &env,
                        &mut functions,
                        &mut classes,
                        &enums,
                        &impl_methods,
                    )? {
                        env.insert(name, new_value);
                        continue;
                    }
                }
                // Handle method calls on objects - need to persist mutations to self
                let (_, update) = handle_method_call_with_self_update(
                    expr,
                    &env,
                    &mut functions,
                    &mut classes,
                    &enums,
                    &impl_methods,
                )?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }

                // Register macro-introduced symbols (#1303)
                // After macro invocation, check if any symbols were introduced
                if let Some(contract_result) = take_macro_introduced_symbols() {
                    // Register introduced functions
                    for (name, func_def) in contract_result.introduced_functions {
                        functions.insert(name.clone(), func_def);
                        // Also add to env as a callable
                        env.insert(
                            name.clone(),
                            Value::Function {
                                name: name.clone(),
                                def: Box::new(functions.get(&name).unwrap().clone()),
                                captured_env: Env::new(),
                            },
                        );
                    }

                    // Register introduced classes
                    for (name, class_def) in contract_result.introduced_classes {
                        classes.insert(name.clone(), class_def);
                        // Add to env as a constructor
                        env.insert(
                            name.clone(),
                            Value::Constructor {
                                class_name: name,
                            },
                        );
                    }

                    // Register introduced types (stored as Nil for now)
                    for (name, _ty) in contract_result.introduced_types {
                        env.insert(name, Value::Nil);
                    }

                    // Register introduced variables
                    for (name, _ty, _is_const) in contract_result.introduced_vars {
                        // Initialize with Nil placeholder
                        // The macro's emit block should assign the actual value
                        env.insert(name, Value::Nil);
                    }
                }
            }
            Node::Break(_) => {
                return Err(CompileError::Semantic("break outside of loop".into()));
            }
            Node::Continue(_) => {
                return Err(CompileError::Semantic("continue outside of loop".into()));
            }
            // Module system nodes
            Node::UseStmt(use_stmt) => {
                // Handle runtime module loading
                use simple_parser::ast::ImportTarget;

                // Determine the binding name (alias or imported item name)
                let binding_name = match &use_stmt.target {
                    ImportTarget::Single(name) => name.clone(),
                    ImportTarget::Aliased { alias, .. } => alias.clone(),
                    ImportTarget::Glob | ImportTarget::Group(_) => {
                        // For glob/group imports, use module name
                        use_stmt.path.segments.last().cloned().unwrap_or_else(|| "module".to_string())
                    }
                };

                // Try to load the module and merge its definitions into global state
                match load_and_merge_module(use_stmt, None, &mut functions, &mut classes, &mut enums) {
                    Ok(value) => {
                        env.insert(binding_name.clone(), value);
                    }
                    Err(_e) => {
                        // Module loading failed - use empty dict as fallback
                        // This allows the program to continue, with errors appearing
                        // when the module members are accessed
                        env.insert(binding_name.clone(), Value::Dict(HashMap::new()));
                    }
                }
            }
            Node::ModDecl(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::AutoImportStmt(_)
            | Node::RequiresCapabilities(_)
            | Node::HandlePool(_)
            | Node::Bitfield(_)
            | Node::AopAdvice(_)
            | Node::DiBinding(_)
            | Node::ArchitectureRule(_)
            | Node::MockDecl(_) => {
                // Module system is handled by the module resolver
                // HandlePool is processed at compile time for allocation
                // Bitfield is processed at compile time for bit-level field access
                // AOP nodes are declarative configuration handled at compile time
                // These are no-ops in the interpreter
            }
        }
    }

    // Check if main is defined as a function and call it
    if let Some(main_func) = functions.get("main").cloned() {
        let result = exec_function(
            &main_func,
            &[],  // No arguments
            &env,
            &mut functions,
            &mut classes,
            &enums,
            &impl_methods,
            None,  // No self context
        )?;
        return result.as_int().map(|v| v as i32);
    }

    // Fall back to checking for `main = <value>` binding
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

fn register_trait_impl(
    registry: &mut HashMap<String, TraitImplRegistry>,
    impl_block: &ImplBlock,
) -> Result<(), CompileError> {
    let is_default = impl_block
        .attributes
        .iter()
        .any(|attr| attr.name == "default");

    let Some(trait_name) = &impl_block.trait_name else {
        if is_default {
            return Err(CompileError::Semantic(
                "#[default] is only valid on trait impls".to_string(),
            ));
        }
        return Ok(());
    };

    let is_blanket = match &impl_block.target_type {
        Type::Simple(name) => impl_block.generic_params.iter().any(|p| p == name),
        _ => false,
    };

    if is_default && !is_blanket {
        return Err(CompileError::Semantic(format!(
            "#[default] impl for trait `{}` must be a blanket impl (impl[T] Trait for T)",
            trait_name
        )));
    }

    let target_key = get_type_name(&impl_block.target_type);
    let entry = registry.entry(trait_name.clone()).or_default();

    if is_blanket {
        if entry.blanket_impl {
            return Err(CompileError::Semantic(format!(
                "duplicate blanket impl for trait `{}`",
                trait_name
            )));
        }
        if !is_default && (!entry.specific_impls.is_empty() || entry.default_blanket_impl) {
            return Err(CompileError::Semantic(format!(
                "overlapping impls for trait `{}`: blanket impl conflicts with existing impls",
                trait_name
            )));
        }
        entry.blanket_impl = true;
        entry.default_blanket_impl = is_default;
        return Ok(());
    }

    if entry.specific_impls.contains(&target_key) {
        return Err(CompileError::Semantic(format!(
            "duplicate impl for trait `{}` and type `{}`",
            trait_name, target_key
        )));
    }

    if entry.blanket_impl && !entry.default_blanket_impl {
        return Err(CompileError::Semantic(format!(
            "overlapping impls for trait `{}`: specific impl for `{}` conflicts with blanket impl",
            trait_name, target_key
        )));
    }

    entry.specific_impls.insert(target_key);
    Ok(())
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
                if let Some((obj_name, new_self)) = update {
                    env.insert(obj_name, new_self);
                }
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
/// Get the import alias from a UseStmt if it exists
fn get_import_alias(use_stmt: &simple_parser::ast::UseStmt) -> Option<String> {
    match &use_stmt.target {
        simple_parser::ast::ImportTarget::Aliased { alias, .. } => Some(alias.clone()),
        _ => None,
    }
}

/// Load a module file, evaluate it, and return exports with captured environment
/// This is needed so that module-level imports are accessible in exported functions
fn load_and_merge_module(
    use_stmt: &simple_parser::ast::UseStmt,
    current_file: Option<&std::path::Path>,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<Value, CompileError> {
    use std::fs;
    use std::path::Path;
    use simple_parser::ast::ImportTarget;

    // Build module path from segments (path only, not the import target)
    let parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // Track what to extract from the module (if anything)
    let import_item_name: Option<String> = match &use_stmt.target {
        ImportTarget::Single(name) => Some(name.clone()),
        ImportTarget::Aliased { name, .. } => Some(name.clone()),
        ImportTarget::Glob => None,
        ImportTarget::Group(_) => {
            // Group imports need special handling
            return Ok(Value::Dict(HashMap::new()));
        }
    };

    // Try to resolve the module path
    let base_dir = current_file
        .and_then(|p| p.parent())
        .unwrap_or(Path::new("."));

    let module_path = resolve_module_path(&parts, base_dir)?;

    // Read and parse the module
    let source = fs::read_to_string(&module_path)
        .map_err(|e| CompileError::Io(format!("Cannot read module: {}", e)))?;

    let mut parser = simple_parser::Parser::new(&source);
    let module = parser.parse()
        .map_err(|e| CompileError::Parse(format!("Cannot parse module: {}", e)))?;

    // Evaluate the module to get its environment (including imports)
    let (module_env, module_exports) = evaluate_module_exports(
        &module.items,
        Some(&module_path),
        functions,
        classes,
        enums,
    )?;

    // Create exports with the module's environment captured
    let mut exports: HashMap<String, Value> = HashMap::new();
    for (name, value) in module_exports {
        match value {
            Value::Function { name: fn_name, def, .. } => {
                // Re-create function with module's env as captured_env
                exports.insert(name, Value::Function {
                    name: fn_name,
                    def,
                    captured_env: module_env.clone(),
                });
            }
            other => {
                exports.insert(name, other);
            }
        }
    }

    // If importing a specific item, extract it from exports
    if let Some(item_name) = import_item_name {
        // Look up the specific item in the module's exports
        if let Some(value) = exports.get(&item_name) {
            return Ok(value.clone());
        } else {
            return Err(CompileError::Runtime(format!(
                "Module does not export '{}'",
                item_name
            )));
        }
    }

    // Otherwise, return the full module dict (for glob imports or module-level imports)
    Ok(Value::Dict(exports))
}

/// Evaluate a module's statements and collect its environment and exports
fn evaluate_module_exports(
    items: &[Node],
    module_path: Option<&std::path::Path>,
    global_functions: &mut HashMap<String, FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
) -> Result<(Env, HashMap<String, Value>), CompileError> {
    let mut env: Env = HashMap::new();
    let mut exports: HashMap<String, Value> = HashMap::new();
    let mut local_functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut local_classes: HashMap<String, ClassDef> = HashMap::new();
    let mut local_enums: Enums = HashMap::new();
    let impl_methods: ImplMethods = HashMap::new();

    // Add builtin types to module environment so they're available in module code
    env.insert("Dict".to_string(), Value::Constructor { class_name: "Dict".to_string() });
    env.insert("List".to_string(), Value::Constructor { class_name: "List".to_string() });
    env.insert("Set".to_string(), Value::Constructor { class_name: "Set".to_string() });
    env.insert("Array".to_string(), Value::Constructor { class_name: "Array".to_string() });
    env.insert("Tuple".to_string(), Value::Constructor { class_name: "Tuple".to_string() });
    env.insert("Option".to_string(), Value::Constructor { class_name: "Option".to_string() });
    env.insert("Result".to_string(), Value::Constructor { class_name: "Result".to_string() });
    env.insert("Some".to_string(), Value::Constructor { class_name: "Some".to_string() });
    env.insert("None".to_string(), Value::Enum { enum_name: "Option".to_string(), variant: "None".to_string(), payload: None });
    env.insert("Ok".to_string(), Value::Constructor { class_name: "Ok".to_string() });
    env.insert("Err".to_string(), Value::Constructor { class_name: "Err".to_string() });

    // First pass: register functions and types
    for item in items {
        match item {
            Node::Function(f) => {
                local_functions.insert(f.name.clone(), f.clone());
                // Don't add "main" from imported modules to global functions
                // to prevent auto-execution when the main script finishes
                if f.name != "main" {
                    global_functions.insert(f.name.clone(), f.clone());
                }
            }
            Node::Class(c) => {
                local_classes.insert(c.name.clone(), c.clone());
                global_classes.insert(c.name.clone(), c.clone());
                exports.insert(c.name.clone(), Value::Constructor {
                    class_name: c.name.clone(),
                });
            }
            Node::Enum(e) => {
                local_enums.insert(e.name.clone(), e.clone());
                global_enums.insert(e.name.clone(), e.clone());
                exports.insert(e.name.clone(), Value::Str(format!("enum:{}", e.name)));
            }
            _ => {}
        }
    }

    // Second pass: process imports and assignments to build the environment
    for item in items {
        match item {
            Node::UseStmt(use_stmt) => {
                // Recursively load imported modules
                use simple_parser::ast::ImportTarget;

                let binding_name = match &use_stmt.target {
                    ImportTarget::Single(name) => name.clone(),
                    ImportTarget::Aliased { alias, .. } => alias.clone(),
                    ImportTarget::Glob | ImportTarget::Group(_) => {
                        use_stmt.path.segments.last().cloned().unwrap_or_else(|| "module".to_string())
                    }
                };

                match load_and_merge_module(use_stmt, module_path, global_functions, global_classes, global_enums) {
                    Ok(value) => {
                        env.insert(binding_name.clone(), value);
                    }
                    Err(_e) => {
                        // Module loading failed - use empty dict
                        env.insert(binding_name.clone(), Value::Dict(HashMap::new()));
                    }
                }
            }
            Node::Let(stmt) => {
                // Evaluate module-level let statements (for global variables)
                use simple_parser::ast::Pattern;
                if let Some(init) = &stmt.value {
                    if let Ok(value) = evaluate_expr(init, &env, &mut local_functions, &mut local_classes, &local_enums, &impl_methods) {
                        // Only handle simple identifier patterns for now
                        if let Pattern::Identifier(name) = &stmt.pattern {
                            env.insert(name.clone(), value);
                        }
                    }
                }
            }
            Node::Assignment(stmt) => {
                // Evaluate module-level assignments
                if let Expr::Identifier(name) = &stmt.target {
                    if let Ok(value) = evaluate_expr(&stmt.value, &env, &mut local_functions, &mut local_classes, &local_enums, &impl_methods) {
                        env.insert(name.clone(), value);
                    }
                }
            }
            _ => {}
        }
    }

    // First pass: Add all module functions to env with empty captured_env
    // This allows functions to reference each other
    for (name, f) in &local_functions {
        env.insert(name.clone(), Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: Env::new(), // Temporary - will be replaced
        });
    }

    // Second pass: Export functions with COMPLETE module environment captured
    // The captured_env now includes globals AND all other functions
    for (name, f) in &local_functions {
        let func_with_env = Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: env.clone(), // Capture complete environment
        };
        exports.insert(name.clone(), func_with_env.clone());

        // Update env with the function that has the complete captured_env
        // so inter-function calls work correctly
        env.insert(name.clone(), func_with_env);
    }

    Ok((env, exports))
}

/// Resolve module path from segments
fn resolve_module_path(parts: &[String], base_dir: &std::path::Path) -> Result<std::path::PathBuf, CompileError> {
    use std::path::PathBuf;

    // Try resolving from base directory first (sibling files)
    let mut resolved = base_dir.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        return Ok(resolved);
    }

    // Try __init__.spl in directory
    let mut init_resolved = base_dir.to_path_buf();
    for part in parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() {
        return Ok(init_resolved);
    }

    // Try stdlib location - walk up directory tree
    let mut current = base_dir.to_path_buf();
    for _ in 0..10 {
        // Try both "simple/std_lib/src" and "std_lib/src" (in case we're already in simple/)
        for stdlib_subpath in &["simple/std_lib/src", "std_lib/src"] {
            let stdlib_candidate = current.join(stdlib_subpath);
            if stdlib_candidate.exists() {
            // Try resolving from stdlib
            let mut stdlib_path = stdlib_candidate.clone();
            for part in parts {
                stdlib_path = stdlib_path.join(part);
            }
            stdlib_path.set_extension("spl");
            if stdlib_path.exists() {
                return Ok(stdlib_path);
            }

            // Also try __init__.spl in stdlib
            let mut stdlib_init_path = stdlib_candidate.clone();
            for part in parts {
                stdlib_init_path = stdlib_init_path.join(part);
            }
            stdlib_init_path = stdlib_init_path.join("__init__");
            stdlib_init_path.set_extension("spl");
            if stdlib_init_path.exists() {
                return Ok(stdlib_init_path);
            }
            }  // End of if stdlib_candidate.exists()
        }  // End of for stdlib_subpath
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    Err(CompileError::Semantic(format!(
        "Cannot resolve module: {}",
        parts.join(".")
    )))
}

/// Merge module definitions into global state and collect exports
fn merge_module_definitions(
    items: &[Node],
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    let mut exports: HashMap<String, Value> = HashMap::new();

    // First pass: collect all definitions into global maps
    for item in items {
        match item {
            Node::Function(f) => {
                // Add to global functions map
                functions.insert(f.name.clone(), f.clone());

                // Add to exports dict
                let func_value = Value::Function {
                    name: f.name.clone(),
                    def: Box::new(f.clone()),
                    captured_env: Env::new(),
                };
                exports.insert(f.name.clone(), func_value);
            }
            Node::Class(c) => {
                // Add to global classes map
                classes.insert(c.name.clone(), c.clone());

                // Add to exports dict
                exports.insert(c.name.clone(), Value::Constructor {
                    class_name: c.name.clone(),
                });
            }
            Node::Enum(e) => {
                // Add to global enums map - this is critical for enum variant access
                enums.insert(e.name.clone(), e.clone());

                // Export the enum type name as well (for type access)
                exports.insert(e.name.clone(), Value::Str(format!("enum:{}", e.name)));
            }
            _ => {}
        }
    }

    Ok(exports)
}

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
