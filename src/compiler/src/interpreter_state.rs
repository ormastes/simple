// Interpreter state management
//
// This module handles:
// - Thread-local state for interpreter execution
// - Execution mode state machine
// - Signal handling (Ctrl-C interrupt)
// - Configuration (DI, AOP)
// - Move tracking for unique pointers

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::{mpsc, Arc, Mutex};

use simple_common::actor::{Message, ThreadSpawner};
use simple_parser::ast::MacroDef;

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::interpreter_unit::*;
use crate::value::Value;

//==============================================================================
// Thread-local state declarations
//==============================================================================

thread_local! {
    pub(crate) static DI_CONFIG: RefCell<Option<Arc<DiConfig>>> = RefCell::new(None);
    pub(crate) static DI_SINGLETONS: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
    pub(crate) static AOP_CONFIG: RefCell<Option<Arc<AopConfig>>> = RefCell::new(None);
    /// Command line arguments passed to the Simple interpreter
    pub(crate) static INTERPRETER_ARGS: RefCell<Vec<String>> = RefCell::new(Vec::new());
    /// Current file being evaluated (for module resolution)
    pub(crate) static CURRENT_FILE: RefCell<Option<PathBuf>> = RefCell::new(None);
}

/// Global interrupt flag for Ctrl-C handling.
///
/// This flag is set to true when the user presses Ctrl-C, signaling that
/// execution should stop gracefully. The interpreter checks this flag
/// at loop iterations and other long-running operations.
///
/// Thread-safe via atomic operations with SeqCst ordering for signal handlers.
pub(crate) static INTERRUPT_REQUESTED: AtomicBool = AtomicBool::new(false);

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

//==============================================================================
// Execution Mode State Machine
//==============================================================================

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

//==============================================================================
// Signal Handling
//==============================================================================

/// Initialize signal handlers for Ctrl-C.
///
/// This function should be called once at program startup to install
/// a handler that sets the INTERRUPT_REQUESTED flag when Ctrl-C is pressed.
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

//==============================================================================
// Configuration Management
//==============================================================================

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
    // Set thread-local storage (for backward compatibility)
    INTERPRETER_ARGS.with(|cell| {
        *cell.borrow_mut() = args.clone();
    });

    // ALSO set global runtime storage (unified approach)
    simple_runtime::value::rt_set_args_vec(&args);
}

/// Get the command line arguments passed to the interpreter
pub fn get_interpreter_args() -> Vec<String> {
    INTERPRETER_ARGS.with(|cell| cell.borrow().clone())
}

/// Set the current file being evaluated (for module resolution)
pub fn set_current_file(path: Option<PathBuf>) {
    CURRENT_FILE.with(|cell| {
        *cell.borrow_mut() = path;
    });
}

/// Get the current file being evaluated
pub fn get_current_file() -> Option<PathBuf> {
    CURRENT_FILE.with(|cell| cell.borrow().clone())
}

//==============================================================================
// Move Tracking (for unique pointer semantics)
//==============================================================================

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
