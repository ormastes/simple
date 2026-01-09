//! Unit system support for the interpreter.
//!
//! This module provides:
//! - SI prefix decomposition and recognition
//! - Unit type validation and constraints checking
//! - Dimensional analysis for compound units
//! - Arithmetic rules for unit operations

use std::collections::HashMap;

use simple_parser::ast::{BinOp, BinaryArithmeticOp, Type, UnaryArithmeticOp, UnaryOp};

use crate::value::Value;

// Thread-local references needed by this module
use crate::interpreter::{
    BASE_UNIT_DIMENSIONS, COMPOUND_UNIT_DIMENSIONS, SI_BASE_UNITS, UNIT_FAMILY_ARITHMETIC,
    UNIT_FAMILY_CONVERSIONS, UNIT_SUFFIX_TO_FAMILY,
};

/// SI prefix definitions: (prefix_char, multiplier)
/// Standard SI prefixes from yotta (10^24) to yocto (10^-24)
pub(crate) const SI_PREFIXES: &[(&str, f64)] = &[
    ("Y", 1e24),  // yotta
    ("Z", 1e21),  // zetta
    ("E", 1e18),  // exa
    ("P", 1e15),  // peta
    ("T", 1e12),  // tera
    ("G", 1e9),   // giga
    ("M", 1e6),   // mega
    ("k", 1e3),   // kilo
    ("h", 1e2),   // hecto
    ("da", 1e1),  // deca
    ("d", 1e-1),  // deci
    ("c", 1e-2),  // centi
    ("m", 1e-3),  // milli (note: conflicts with meter, handled specially)
    ("u", 1e-6),  // micro (ASCII u for µ)
    ("μ", 1e-6),  // micro (Unicode)
    ("n", 1e-9),  // nano
    ("p", 1e-12), // pico
    ("f", 1e-15), // femto
    ("a", 1e-18), // atto
    ("z", 1e-21), // zepto
    ("y", 1e-24), // yocto
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
    let is_family = UNIT_FAMILY_CONVERSIONS.with(|cell| cell.borrow().contains_key(type_name));
    if is_family {
        return true;
    }
    // Check if it's a compound unit (like "velocity", "acceleration")
    COMPOUND_UNIT_DIMENSIONS.with(|cell| cell.borrow().contains_key(type_name))
}

/// Validate that a value matches a unit type annotation
/// Returns Ok(()) if valid, Err with message if invalid
pub(crate) fn validate_unit_type(value: &Value, expected_type: &str) -> Result<(), String> {
    match value {
        Value::Unit { family, suffix, .. } => {
            // Check if the unit's family matches the expected type
            let actual_family = family
                .as_ref()
                .map(|s| s.as_str())
                .unwrap_or(suffix.as_str());
            if actual_family == expected_type {
                Ok(())
            } else {
                // Check if the suffix itself indicates membership in the expected family
                let suffix_family =
                    UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned());
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
            expected_type,
            value.type_name()
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
        Value::Int(n) => {
            return validate_int_constraints(*n, unit_name, constraints).map(Value::Int)
        }
        Value::Float(f) => {
            return validate_float_constraints(*f, unit_name, constraints).map(Value::Float)
        }
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
                simple_parser::ast::OverflowBehavior::Checked
                | simple_parser::ast::OverflowBehavior::Default => {
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
fn validate_int_constraints(
    value: i64,
    unit_name: &str,
    constraints: &simple_parser::ast::UnitReprConstraints,
) -> Result<i64, String> {
    if let Some((min, max)) = constraints.range {
        if value < min || value > max {
            match constraints.overflow {
                simple_parser::ast::OverflowBehavior::Checked
                | simple_parser::ast::OverflowBehavior::Default => {
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
fn validate_float_constraints(
    value: f64,
    unit_name: &str,
    constraints: &simple_parser::ast::UnitReprConstraints,
) -> Result<f64, String> {
    if let Some((min, max)) = constraints.range {
        let min_f = min as f64;
        let max_f = max as f64;
        if value < min_f || value > max_f {
            match constraints.overflow {
                simple_parser::ast::OverflowBehavior::Checked
                | simple_parser::ast::OverflowBehavior::Default => {
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
        Value::Unit {
            value: inner,
            suffix,
            family,
        } => {
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
pub(crate) fn type_to_family_name(ty: &Type) -> String {
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
                    } else if let Some(compound_name) =
                        find_compound_unit_for_dimension(&result_dim)
                    {
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
pub(crate) fn check_unit_unary_op(family: &str, op: UnaryOp) -> Result<Option<String>, String> {
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
