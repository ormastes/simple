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

thread_local! {
    pub(crate) static DI_CONFIG: RefCell<Option<Arc<DiConfig>>> = RefCell::new(None);
    pub(crate) static DI_SINGLETONS: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
    pub(crate) static AOP_CONFIG: RefCell<Option<Arc<AopConfig>>> = RefCell::new(None);
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

/// SI prefix definitions: (prefix_char, multiplier)
/// Standard SI prefixes from yotta (10^24) to yocto (10^-24)
pub(crate) const SI_PREFIXES: &[(&str, f64)] = &[
    ("Y", 1e24),   // yotta
    ("Z", 1e21),   // zetta
    ("E", 1e18),   // exa
    ("P", 1e15),   // peta
    ("T", 1e12),   // tera
    ("G", 1e9),    // giga
    ("M", 1e6),    // mega
    ("k", 1e3),    // kilo
    ("h", 1e2),    // hecto
    ("da", 1e1),   // deca
    ("d", 1e-1),   // deci
    ("c", 1e-2),   // centi
    ("m", 1e-3),   // milli (note: conflicts with meter, handled specially)
    ("u", 1e-6),   // micro (ASCII u for µ)
    ("μ", 1e-6),   // micro (Unicode)
    ("n", 1e-9),   // nano
    ("p", 1e-12),  // pico
    ("f", 1e-15),  // femto
    ("a", 1e-18),  // atto
    ("z", 1e-21),  // zepto
    ("y", 1e-24),  // yocto
];

/// Try to decompose a unit suffix into SI prefix + base unit
/// Returns (prefix_multiplier, base_suffix, family_name) if successful
pub(crate) fn decompose_si_prefix(suffix: &str) -> Option<(f64, String, String)> {
    SI_BASE_UNITS.with(|cell| {
        let base_units = cell.borrow();

        // Try each SI prefix (longest first for "da")
        for &(prefix, multiplier) in SI_PREFIXES {
            if suffix.starts_with(prefix) && suffix.len() > prefix.len() {
                let base = &suffix[prefix.len()..];

                // Special case: avoid "m" + "m" = "mm" being parsed as milli-meter
                // when "mm" might be a directly defined unit
                // Check if the full suffix is directly registered first
                if UNIT_SUFFIX_TO_FAMILY.with(|c| c.borrow().contains_key(suffix)) {
                    return None;
                }

                // Check if base unit is registered for SI prefixes
                if let Some(family) = base_units.get(base) {
                    return Some((multiplier, base.to_string(), family.clone()));
                }
            }
        }
        None
    })
}

/// Check if a type name is a registered unit family or compound unit
/// Returns true if the type name refers to a unit type that can be used for type checking
pub(crate) fn is_unit_type(type_name: &str) -> bool {
    // Check if it's a unit family (like "length", "time")
    let is_family = UNIT_FAMILY_CONVERSIONS.with(|cell| {
        cell.borrow().contains_key(type_name)
    });
    if is_family {
        return true;
    }
    // Check if it's a compound unit (like "velocity", "acceleration")
    COMPOUND_UNIT_DIMENSIONS.with(|cell| {
        cell.borrow().contains_key(type_name)
    })
}

/// Validate that a value matches a unit type annotation
/// Returns Ok(()) if valid, Err with message if invalid
pub(crate) fn validate_unit_type(value: &Value, expected_type: &str) -> Result<(), String> {
    match value {
        Value::Unit { family, suffix, .. } => {
            // Check if the unit's family matches the expected type
            let actual_family = family.as_ref().map(|s| s.as_str()).unwrap_or(suffix.as_str());
            if actual_family == expected_type {
                Ok(())
            } else {
                // Check if the suffix itself indicates membership in the expected family
                let suffix_family = UNIT_SUFFIX_TO_FAMILY.with(|cell| {
                    cell.borrow().get(suffix).cloned()
                });
                if suffix_family.as_deref() == Some(expected_type) {
                    Ok(())
                } else {
                    Err(format!(
                        "expected unit type '{}', got '{}' (family: {})",
                        expected_type, suffix, actual_family
                    ))
                }
            }
        }
        _ => Err(format!(
            "expected unit type '{}', got non-unit value of type '{}'",
            expected_type, value.type_name()
        )),
    }
}

/// Validate unit type constraints (range bounds, overflow behavior)
/// Returns Ok(value) with potentially modified value (for saturate/wrap), Err for checked mode violations
pub(crate) fn validate_unit_constraints(
    value: Value,
    unit_name: &str,
    constraints: &simple_parser::ast::UnitReprConstraints,
) -> Result<Value, String> {
    // Extract the numeric value from the Unit
    let inner_value = match &value {
        Value::Unit { value: inner, .. } => inner.as_ref(),
        Value::Int(n) => return validate_int_constraints(*n, unit_name, constraints).map(Value::Int),
        Value::Float(f) => return validate_float_constraints(*f, unit_name, constraints).map(Value::Float),
        _ => return Ok(value), // Non-numeric types pass through unchanged
    };

    // Get the numeric value for range checking
    let numeric = match inner_value {
        Value::Int(n) => *n as f64,
        Value::Float(f) => *f,
        _ => return Ok(value), // Non-numeric inner types pass through
    };

    // Check range constraints if present
    if let Some((min, max)) = constraints.range {
        let min_f = min as f64;
        let max_f = max as f64;

        if numeric < min_f || numeric > max_f {
            match constraints.overflow {
                simple_parser::ast::OverflowBehavior::Checked | simple_parser::ast::OverflowBehavior::Default => {
                    return Err(format!(
                        "unit '{}' value {} out of range [{}, {}]",
                        unit_name, numeric, min, max
                    ));
                }
                simple_parser::ast::OverflowBehavior::Saturate => {
                    // Clamp to range bounds
                    let clamped = if numeric < min_f { min_f } else { max_f };
                    return Ok(clamp_unit_value(value, clamped));
                }
                simple_parser::ast::OverflowBehavior::Wrap => {
                    // Wrap around using modulo
                    let range = max_f - min_f + 1.0;
                    let wrapped = min_f + ((numeric - min_f).rem_euclid(range));
                    return Ok(clamp_unit_value(value, wrapped));
                }
            }
        }
    }

    Ok(value)
}

/// Apply constraints to an integer value
fn validate_int_constraints(value: i64, unit_name: &str, constraints: &simple_parser::ast::UnitReprConstraints) -> Result<i64, String> {
    if let Some((min, max)) = constraints.range {
        if value < min || value > max {
            match constraints.overflow {
                simple_parser::ast::OverflowBehavior::Checked | simple_parser::ast::OverflowBehavior::Default => {
                    return Err(format!(
                        "unit '{}' value {} out of range [{}, {}]",
                        unit_name, value, min, max
                    ));
                }
                simple_parser::ast::OverflowBehavior::Saturate => {
                    return Ok(value.clamp(min, max));
                }
                simple_parser::ast::OverflowBehavior::Wrap => {
                    let range = max - min + 1;
                    return Ok(min + ((value - min).rem_euclid(range)));
                }
            }
        }
    }
    Ok(value)
}

/// Apply constraints to a float value
fn validate_float_constraints(value: f64, unit_name: &str, constraints: &simple_parser::ast::UnitReprConstraints) -> Result<f64, String> {
    if let Some((min, max)) = constraints.range {
        let min_f = min as f64;
        let max_f = max as f64;
        if value < min_f || value > max_f {
            match constraints.overflow {
                simple_parser::ast::OverflowBehavior::Checked | simple_parser::ast::OverflowBehavior::Default => {
                    return Err(format!(
                        "unit '{}' value {} out of range [{}, {}]",
                        unit_name, value, min, max
                    ));
                }
                simple_parser::ast::OverflowBehavior::Saturate => {
                    return Ok(value.clamp(min_f, max_f));
                }
                simple_parser::ast::OverflowBehavior::Wrap => {
                    let range = max_f - min_f + 1.0;
                    return Ok(min_f + ((value - min_f).rem_euclid(range)));
                }
            }
        }
    }
    Ok(value)
}

/// Helper to create a new Unit value with clamped inner value
fn clamp_unit_value(original: Value, new_numeric: f64) -> Value {
    match original {
        Value::Unit { value: inner, suffix, family } => {
            let new_inner = match inner.as_ref() {
                Value::Int(_) => Value::Int(new_numeric as i64),
                Value::Float(_) => Value::Float(new_numeric),
                _ => *inner,
            };
            Value::Unit {
                value: Box::new(new_inner),
                suffix,
                family,
            }
        }
        _ => original,
    }
}

/// Represents a physical dimension as exponents of base units
/// e.g., velocity = length^1 * time^-1 is represented as {length: 1, time: -1}
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct Dimension {
    /// Maps base unit name -> exponent
    pub exponents: HashMap<String, i32>,
}

impl Dimension {
    /// Create a new dimension from a single base unit with exponent 1
    pub fn base(name: &str) -> Self {
        let mut exponents = HashMap::new();
        exponents.insert(name.to_string(), 1);
        Dimension { exponents }
    }

    /// Multiply two dimensions (add exponents)
    pub fn mul(&self, other: &Dimension) -> Dimension {
        let mut result = self.exponents.clone();
        for (unit, exp) in &other.exponents {
            *result.entry(unit.clone()).or_insert(0) += exp;
        }
        // Remove zero exponents
        result.retain(|_, v| *v != 0);
        Dimension { exponents: result }
    }

    /// Divide two dimensions (subtract exponents)
    pub fn div(&self, other: &Dimension) -> Dimension {
        let mut result = self.exponents.clone();
        for (unit, exp) in &other.exponents {
            *result.entry(unit.clone()).or_insert(0) -= exp;
        }
        // Remove zero exponents
        result.retain(|_, v| *v != 0);
        Dimension { exponents: result }
    }

    /// Raise dimension to a power (multiply all exponents)
    pub fn pow(&self, power: i32) -> Dimension {
        let mut result = HashMap::new();
        for (unit, exp) in &self.exponents {
            let new_exp = exp * power;
            if new_exp != 0 {
                result.insert(unit.clone(), new_exp);
            }
        }
        Dimension { exponents: result }
    }

    /// Check if this dimension is dimensionless (all exponents are zero)
    pub fn is_dimensionless(&self) -> bool {
        self.exponents.is_empty()
    }

    /// Convert a UnitExpr AST to a Dimension
    pub fn from_unit_expr(expr: &simple_parser::ast::UnitExpr) -> Self {
        use simple_parser::ast::UnitExpr;
        match expr {
            UnitExpr::Base(name) => {
                // Look up if this is a known dimension, otherwise treat as base
                BASE_UNIT_DIMENSIONS.with(|cell| {
                    cell.borrow()
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| Dimension::base(name))
                })
            }
            UnitExpr::Mul(left, right) => {
                let left_dim = Dimension::from_unit_expr(left);
                let right_dim = Dimension::from_unit_expr(right);
                left_dim.mul(&right_dim)
            }
            UnitExpr::Div(left, right) => {
                let left_dim = Dimension::from_unit_expr(left);
                let right_dim = Dimension::from_unit_expr(right);
                left_dim.div(&right_dim)
            }
            UnitExpr::Pow(base, power) => {
                let base_dim = Dimension::from_unit_expr(base);
                base_dim.pow(*power)
            }
        }
    }
}

/// Look up the dimension for a unit family name
pub(crate) fn get_unit_dimension(family: &str) -> Option<Dimension> {
    // First check compound units
    let compound = COMPOUND_UNIT_DIMENSIONS.with(|cell| cell.borrow().get(family).cloned());
    if compound.is_some() {
        return compound;
    }
    // Then check base units
    BASE_UNIT_DIMENSIONS.with(|cell| cell.borrow().get(family).cloned())
}

/// Find a compound unit name that matches the given dimension
pub(crate) fn find_compound_unit_for_dimension(dim: &Dimension) -> Option<String> {
    COMPOUND_UNIT_DIMENSIONS.with(|cell| {
        for (name, unit_dim) in cell.borrow().iter() {
            if unit_dim == dim {
                return Some(name.clone());
            }
        }
        None
    })
}

/// Stores arithmetic rules for a unit family
#[derive(Debug, Clone, Default)]
pub(crate) struct UnitArithmeticRules {
    /// Binary rules: (op, operand_type) -> result_type
    pub binary_rules: Vec<(BinaryArithmeticOp, String, String)>,
    /// Unary rules: op -> result_type
    pub unary_rules: Vec<(UnaryArithmeticOp, String)>,
}

/// Convert a Type to a family name string (for arithmetic rule storage)
fn type_to_family_name(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        _ => format!("{:?}", ty), // Fallback for complex types
    }
}

/// Check if a binary operation is allowed between two unit values
/// Returns Ok(result_family) if allowed, Err with error message if not
pub(crate) fn check_unit_binary_op(
    left_family: &str,
    right_family: &str,
    op: BinOp,
) -> Result<Option<String>, String> {
    // Convert BinOp to BinaryArithmeticOp
    let arith_op = match op {
        BinOp::Add => BinaryArithmeticOp::Add,
        BinOp::Sub => BinaryArithmeticOp::Sub,
        BinOp::Mul => BinaryArithmeticOp::Mul,
        BinOp::Div => BinaryArithmeticOp::Div,
        BinOp::Mod => BinaryArithmeticOp::Mod,
        // Comparison ops are always allowed between same-family units
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
            if left_family == right_family {
                return Ok(None); // Returns bool, not a unit
            } else {
                return Err(format!(
                    "Cannot compare '{}' and '{}' - different unit families",
                    left_family, right_family
                ));
            }
        }
        // Other ops not applicable to units
        _ => return Ok(None),
    };

    // Look up arithmetic rules for the left operand's family
    UNIT_FAMILY_ARITHMETIC.with(|cell| {
        let rules = cell.borrow();
        if let Some(family_rules) = rules.get(left_family) {
            // This family has explicit rules - enforce them strictly
            // Check if there's a rule allowing this operation
            for (rule_op, operand_type, result_type) in &family_rules.binary_rules {
                if *rule_op == arith_op && operand_type == right_family {
                    return Ok(Some(result_type.clone()));
                }
            }
            // No rule found for this operation
            Err(format!(
                "Operation '{:?}' not allowed: '{}' has no rule for '{:?}({}) -> ?'",
                op, left_family, arith_op, right_family
            ))
        } else {
            // No arithmetic rules defined for this family
            // For add/sub: require same family (permissive mode for ad-hoc units)
            // For mul/div: use dimensional analysis to compute result
            match arith_op {
                BinaryArithmeticOp::Add | BinaryArithmeticOp::Sub => {
                    if left_family == right_family {
                        // Same family - allow and return the same family
                        Ok(Some(left_family.to_string()))
                    } else {
                        Err(format!(
                            "Cannot perform {:?} between '{}' and '{}' - different unit families",
                            op, left_family, right_family
                        ))
                    }
                }
                BinaryArithmeticOp::Mul | BinaryArithmeticOp::Div => {
                    // Dimensional analysis: compute the resulting dimension
                    let left_dim = get_unit_dimension(left_family)
                        .unwrap_or_else(|| Dimension::base(left_family));
                    let right_dim = get_unit_dimension(right_family)
                        .unwrap_or_else(|| Dimension::base(right_family));

                    let result_dim = if arith_op == BinaryArithmeticOp::Mul {
                        left_dim.mul(&right_dim)
                    } else {
                        left_dim.div(&right_dim)
                    };

                    // Look up if there's a known compound unit for this dimension
                    if result_dim.is_dimensionless() {
                        // Result is dimensionless (e.g., length / length)
                        Ok(None) // Returns a plain number, not a unit
                    } else if let Some(compound_name) = find_compound_unit_for_dimension(&result_dim) {
                        // Found a matching compound unit
                        Ok(Some(compound_name))
                    } else {
                        // No matching compound unit - return a dimension string representation
                        let dim_str = format!("{:?}", result_dim.exponents);
                        Ok(Some(dim_str))
                    }
                }
                BinaryArithmeticOp::Mod => {
                    // Modulo only works with same family
                    if left_family == right_family {
                        Ok(Some(left_family.to_string()))
                    } else {
                        Err(format!(
                            "Cannot perform {:?} between '{}' and '{}' - different unit families",
                            op, left_family, right_family
                        ))
                    }
                }
            }
        }
    })
}

/// Check if a unary operation is allowed for a unit value
/// Returns Ok(result_family) if allowed, Err with error message if not
pub(crate) fn check_unit_unary_op(
    family: &str,
    op: UnaryOp,
) -> Result<Option<String>, String> {
    // Convert UnaryOp to UnaryArithmeticOp
    let arith_op = match op {
        UnaryOp::Neg => UnaryArithmeticOp::Neg,
        // Other unary ops not handled as arithmetic
        _ => return Ok(None),
    };

    // Look up arithmetic rules for the family
    UNIT_FAMILY_ARITHMETIC.with(|cell| {
        let rules = cell.borrow();
        if let Some(family_rules) = rules.get(family) {
            // This family has explicit rules - enforce them strictly
            // Check if there's a rule allowing this operation
            for (rule_op, result_type) in &family_rules.unary_rules {
                if *rule_op == arith_op {
                    return Ok(Some(result_type.clone()));
                }
            }
            // No rule found for this operation
            Err(format!(
                "Operation '{:?}' not allowed for unit family '{}'",
                op, family
            ))
        } else {
            // No arithmetic rules defined for this family
            // Allow negation by default (permissive mode for ad-hoc units)
            Ok(Some(family.to_string()))
        }
    })
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
                                    &arg.value,
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
                    if let Some((name, new_value)) = handle_functional_update(
                        target,
                        method,
                        args,
                        &env,
                        &functions,
                        &classes,
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
                    &functions,
                    &classes,
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
            // Module system nodes - parsed but not interpreted at this level
            // Module resolution happens before interpretation
            Node::ModDecl(_)
            | Node::UseStmt(_)
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
    if let Some(main_func) = functions.get("main") {
        let result = exec_function(
            main_func,
            &[],  // No arguments
            &env,
            &functions,
            &classes,
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

/// Execute a block in a function context, supporting implicit return.
/// If the last statement is an expression, its value is captured and returned.
pub(crate) fn exec_block_fn(
    block: &Block,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
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

// Expression evaluation (extracted for maintainability)
include!("interpreter_expr.rs");

// Include helper functions (method dispatch, array/dict ops, pattern binding, slicing)
include!("interpreter_helpers.rs");

// Include the rest of the interpreter functions
include!("interpreter_call.rs");
include!("interpreter_method.rs");
include!("interpreter_macro.rs");
include!("interpreter_extern.rs");
include!("interpreter_native_io.rs");
include!("interpreter_native_net.rs");
include!("interpreter_context.rs");
