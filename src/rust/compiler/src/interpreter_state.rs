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
use std::sync::atomic::{AtomicBool, AtomicU64};
use std::sync::{mpsc, Arc, Mutex};

use simple_common::actor::{Message, ThreadSpawner};
use simple_parser::ast::{Block, MacroDef, Type};

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::interpreter_unit::*;
use crate::value::Value;

/// Information about a literal function for custom string suffix handling.
///
/// Literal functions allow explicit override of suffix → type mapping:
/// ```simple
/// literal fn _re(s: text) -> Regex:
///     Regex.compile(s)
/// ```
#[derive(Debug, Clone)]
pub struct LiteralFunctionInfo {
    /// The suffix without leading underscore (e.g., "re" for _re)
    pub suffix: String,
    /// The return type of the literal function
    pub return_type: Option<Type>,
    /// The parameter name for the string value
    pub param_name: String,
    /// The function body
    pub body: Block,
}

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
    /// Interface bindings for static polymorphism (trait_name -> impl_type_name)
    /// When a binding exists, method calls on trait objects use static dispatch
    /// to the bound implementation type.
    pub(crate) static INTERFACE_BINDINGS: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
}

/// Global interrupt flag for Ctrl-C handling.
///
/// This flag is set to true when the user presses Ctrl-C, signaling that
/// execution should stop gracefully. The interpreter checks this flag
/// at loop iterations and other long-running operations.
///
/// Thread-safe via atomic operations with SeqCst ordering for signal handlers.
pub(crate) static INTERRUPT_REQUESTED: AtomicBool = AtomicBool::new(false);

/// Global debug mode flag.
///
/// When set to true, debug print statements (dprint) will output.
/// When false, dprint calls are silently ignored.
/// Thread-safe via atomic operations.
/// Default: true in debug builds, false in release builds.
#[cfg(debug_assertions)]
pub(crate) static DEBUG_MODE: AtomicBool = AtomicBool::new(true);

#[cfg(not(debug_assertions))]
pub(crate) static DEBUG_MODE: AtomicBool = AtomicBool::new(false);

/// Execution limit to prevent infinite loops (default: 10 million operations)
pub(crate) static EXECUTION_LIMIT: AtomicU64 = AtomicU64::new(10_000_000);

/// Current instruction count (reset per execution)
pub(crate) static INSTRUCTION_COUNT: AtomicU64 = AtomicU64::new(0);

/// Whether execution limit checking is enabled (default: true in debug builds)
#[cfg(debug_assertions)]
pub(crate) static EXECUTION_LIMIT_ENABLED: AtomicBool = AtomicBool::new(true);

#[cfg(not(debug_assertions))]
pub(crate) static EXECUTION_LIMIT_ENABLED: AtomicBool = AtomicBool::new(false);

thread_local! {
    pub(crate) static ACTOR_SPAWNER: ThreadSpawner = ThreadSpawner::new();
    pub(crate) static ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = RefCell::new(None);
    pub(crate) static ACTOR_OUTBOX: RefCell<Option<mpsc::Sender<Message>>> = RefCell::new(None);
    pub(crate) static CONST_NAMES: RefCell<std::collections::HashSet<String>> = RefCell::new(std::collections::HashSet::new());
    /// Immutable variables tracked by naming pattern (lowercase without underscore suffix)
    /// These cannot be reassigned but support functional update with ->
    pub(crate) static IMMUTABLE_VARS: RefCell<std::collections::HashSet<String>> = RefCell::new(std::collections::HashSet::new());
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
    /// BDD Test Registry - shared across all modules that import spec.registry
    /// This ensures that describe/context/it blocks register to the same location
    /// regardless of how the registry module is imported.
    pub(crate) static BDD_REGISTRY_GROUPS: RefCell<Vec<Value>> = RefCell::new(Vec::new());
    /// BDD Context definitions registry (for context_def blocks)
    pub(crate) static BDD_REGISTRY_CONTEXTS: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
    /// BDD Shared examples registry (for shared_examples blocks)
    pub(crate) static BDD_REGISTRY_SHARED: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
    /// Literal function registry for custom string suffix → type mapping.
    /// Maps suffix (without leading underscore) to LiteralFunctionInfo.
    /// Example: "re" → LiteralFunctionInfo for `literal fn _re(s: text) -> Regex: ...`
    pub(crate) static LITERAL_FUNCTIONS: RefCell<HashMap<String, LiteralFunctionInfo>> = RefCell::new(HashMap::new());
    /// Tracks whether we're currently executing inside an immutable fn method.
    /// When true, self.field = value assignments should error.
    /// This is set when entering a fn method (not me method) and cleared when leaving.
    pub(crate) static IN_IMMUTABLE_FN_METHOD: RefCell<bool> = RefCell::new(false);
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
// Debug Mode Management
//==============================================================================

/// Enable or disable debug mode.
///
/// When debug mode is enabled, dprint() statements will output.
/// When disabled, dprint() calls are silently ignored.
pub fn set_debug_mode(enabled: bool) {
    DEBUG_MODE.store(enabled, std::sync::atomic::Ordering::SeqCst);
}

/// Check if debug mode is enabled.
///
/// Returns true if debug printing is enabled.
#[inline]
pub fn is_debug_mode() -> bool {
    DEBUG_MODE.load(std::sync::atomic::Ordering::Relaxed)
}

//==============================================================================
// Execution Limit Management
//==============================================================================

/// Check execution limit and increment counter.
/// Returns error if limit exceeded.
#[inline]
pub fn check_execution_limit() -> Result<(), crate::error::CompileError> {
    if !is_execution_limit_enabled() {
        return Ok(());
    }
    let count = INSTRUCTION_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let limit = EXECUTION_LIMIT.load(std::sync::atomic::Ordering::Relaxed);
    if limit > 0 && count >= limit {
        return Err(crate::error::CompileError::ExecutionLimitExceeded {
            limit,
            message: format!("Execution limit of {} operations exceeded", limit),
        });
    }
    Ok(())
}

/// Reset execution count (call at start of each file/test)
pub fn reset_execution_count() {
    INSTRUCTION_COUNT.store(0, std::sync::atomic::Ordering::SeqCst);
}

/// Set execution limit (0 = no limit)
pub fn set_execution_limit(limit: u64) {
    EXECUTION_LIMIT.store(limit, std::sync::atomic::Ordering::SeqCst);
}

/// Get current execution count
pub fn get_execution_count() -> u64 {
    INSTRUCTION_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}

/// Enable or disable execution limit checking
pub fn set_execution_limit_enabled(enabled: bool) {
    EXECUTION_LIMIT_ENABLED.store(enabled, std::sync::atomic::Ordering::SeqCst);
}

/// Check if execution limit is enabled
#[inline]
pub fn is_execution_limit_enabled() -> bool {
    EXECUTION_LIMIT_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
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

//==============================================================================
// Full State Reset (for test isolation)
//==============================================================================

/// Clear all thread-local interpreter state.
///
/// This function should be called before each test file to prevent memory leaks
/// and state pollution between tests. It clears:
/// - BDD registries (test groups, contexts, shared examples)
/// - Module globals
/// - DI singletons
/// - Moved variables tracking
/// - Const names
/// - Immutable variables
/// - Extern functions
/// - User macros
/// - Unit system registries
/// - Literal functions
/// - Interface bindings
///
/// Note: Module cache is cleared separately via `clear_module_cache()`.
pub fn clear_interpreter_state() {
    // Clear BDD registries (accumulate test definitions)
    BDD_REGISTRY_GROUPS.with(|cell| cell.borrow_mut().clear());
    BDD_REGISTRY_CONTEXTS.with(|cell| cell.borrow_mut().clear());
    BDD_REGISTRY_SHARED.with(|cell| cell.borrow_mut().clear());

    // Clear module globals (mutable module-level variables)
    MODULE_GLOBALS.with(|cell| cell.borrow_mut().clear());

    // Clear DI singletons
    DI_SINGLETONS.with(|cell| cell.borrow_mut().clear());

    // Clear variable tracking
    MOVED_VARS.with(|cell| cell.borrow_mut().clear());
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    IMMUTABLE_VARS.with(|cell| cell.borrow_mut().clear());
    EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().clear());

    // Clear user macros
    USER_MACROS.with(|cell| cell.borrow_mut().clear());
    MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().clear());

    // Clear unit system registries
    UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_CONVERSIONS.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_ARITHMETIC.with(|cell| cell.borrow_mut().clear());
    COMPOUND_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    BASE_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    SI_BASE_UNITS.with(|cell| cell.borrow_mut().clear());

    // Clear literal functions
    LITERAL_FUNCTIONS.with(|cell| cell.borrow_mut().clear());

    // Clear interface bindings
    INTERFACE_BINDINGS.with(|cell| cell.borrow_mut().clear());

    // Reset execution mode to Normal
    EXECUTION_MODE.with(|cell| *cell.borrow_mut() = ExecutionMode::Normal);

    // Clear context-related state
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = None);
    CONTEXT_VAR_NAME.with(|cell| *cell.borrow_mut() = None);
    GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = None);

    // Reset immutable fn method tracking
    IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow_mut() = false);
}
