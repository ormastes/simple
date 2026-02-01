//! Pattern matching functions for the interpreter
//!
//! This module provides pattern matching implementations used by match expressions
//! and other pattern-based constructs.

use std::collections::HashMap;

use crate::error::CompileError;
use crate::value::Value;
use simple_parser::ast::{Expr, FStringPart, Pattern, Type};

use super::{Enums, BLOCK_SCOPED_ENUMS};

/// Check if a pattern is a catch-all that covers any value.
pub(crate) fn is_catch_all_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(_) | Pattern::MutIdentifier(_) | Pattern::MoveIdentifier(_) => true,
        Pattern::Or(patterns) => patterns.iter().any(is_catch_all_pattern),
        Pattern::Typed { pattern, .. } => is_catch_all_pattern(pattern),
        _ => false,
    }
}

/// Match a sequence pattern (tuple or array) against a value.
pub(super) fn match_sequence_pattern(
    value: &Value,
    patterns: &[Pattern],
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
    is_tuple: bool,
) -> Result<bool, CompileError> {
    let values = if is_tuple {
        if let Value::Tuple(vals) = value {
            vals
        } else {
            return Ok(false);
        }
    } else if let Value::Array(vals) = value {
        vals
    } else {
        return Ok(false);
    };

    // Check for Rest pattern to support variable-length matching
    // e.g., [first, ..rest] or [first, second, ..]
    let rest_index = patterns.iter().position(|p| matches!(p, Pattern::Rest));

    if let Some(rest_idx) = rest_index {
        // Patterns before the rest
        let before_rest = &patterns[..rest_idx];
        // Patterns after the rest (if any - skip the Rest itself)
        let after_rest = if rest_idx + 1 < patterns.len() {
            &patterns[rest_idx + 1..]
        } else {
            &[]
        };

        // Minimum values needed: before_rest.len() + after_rest.len()
        let min_needed = before_rest.len() + after_rest.len();
        if values.len() < min_needed {
            return Ok(false);
        }

        // Match patterns before rest
        for (pat, val) in before_rest.iter().zip(values.iter()) {
            if !pattern_matches(pat, val, bindings, enums)? {
                return Ok(false);
            }
        }

        // Match patterns after rest (from the end)
        for (i, pat) in after_rest.iter().enumerate() {
            let val_idx = values.len() - after_rest.len() + i;
            if !pattern_matches(pat, &values[val_idx], bindings, enums)? {
                return Ok(false);
            }
        }

        // Collect rest elements
        let rest_start = before_rest.len();
        let rest_end = values.len() - after_rest.len();
        let rest_values: Vec<Value> = values[rest_start..rest_end].to_vec();

        // If there's an identifier after .., bind it to the rest
        // Look for NamedRest pattern which would be Pattern::Identifier after Rest
        // For now, rest patterns just match (they don't bind)
        // A future enhancement could support [first, ..rest] with named rest

        // Store rest in a special binding if followed by an identifier
        // This is a simplified approach - full support would need parser changes
        bindings.insert("__rest__".to_string(), Value::Array(rest_values));

        Ok(true)
    } else {
        // No rest pattern - exact match required
        if patterns.len() != values.len() {
            return Ok(false);
        }

        for (pat, val) in patterns.iter().zip(values.iter()) {
            if !pattern_matches(pat, val, bindings, enums)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// Check if a pattern matches a value, populating bindings.
pub(crate) fn pattern_matches(
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
) -> Result<bool, CompileError> {
    match pattern {
        Pattern::Wildcard => Ok(true),

        Pattern::Identifier(name) => {
            // Special case: if matching an enum and the identifier matches a variant name,
            // treat it as a unit variant pattern (not a binding)
            if let Value::Enum {
                enum_name,
                variant,
                payload,
            } = value
            {
                // Check if this identifier is a known variant of the enum
                // Look in both module-level enums and block-scoped enums
                let enum_def = enums
                    .get(enum_name)
                    .cloned()
                    .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()));
                if let Some(enum_def) = enum_def {
                    let is_variant = enum_def.variants.iter().any(|v| &v.name == name);
                    if is_variant {
                        // This is a unit variant pattern - match only if variant matches
                        // and the value has no payload (unit variant)
                        return Ok(variant == name && payload.is_none());
                    }
                }
            }
            // Normal identifier pattern - bind the value
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MutIdentifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MoveIdentifier(name) => {
            // Move pattern - transfers ownership during pattern matching
            // For the interpreter, this behaves the same as a regular binding
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::Literal(lit_expr) => {
            match lit_expr.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => {
                    if let Value::Int(v) = value {
                        Ok(*v == *i)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Float(f) | Expr::TypedFloat(f, _) => {
                    if let Value::Float(v) = value {
                        Ok((*v - *f).abs() < f64::EPSILON)
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
                // Handle FString patterns (strings parsed as f-strings with only literal parts)
                Expr::FString { parts, .. } => {
                    // Build the full string from literal parts
                    let mut pattern_str = String::new();
                    for part in parts {
                        match part {
                            FStringPart::Literal(s) => pattern_str.push_str(&s),
                            FStringPart::Expr(_) => {
                                // FStrings with expressions cannot be used as patterns
                                return Ok(false);
                            }
                        }
                    }
                    if let Value::Str(v) = value {
                        Ok(v == &pattern_str)
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
                Expr::Nil => Ok(matches!(value, Value::Nil) || matches!(value, Value::Enum { ref variant, .. } if variant == "None")),
                _ => Ok(false),
            }
        }

        Pattern::Enum {
            name: enum_name,
            variant,
            payload,
        } => {
            // Special case: Nil matches Option::None
            if matches!(value, Value::Nil)
                && (enum_name == "Option" || enum_name == "_")
                && variant == "None"
                && payload.is_none()
            {
                return Ok(true);
            }
            if let Value::Enum {
                enum_name: ve,
                variant: vv,
                payload: value_payload,
            } = value
            {
                // Handle "_" placeholder for unqualified user-defined enum variants
                // When pattern has enum_name="_", match any enum with the correct variant
                let enum_matches = enum_name == "_" || enum_name == ve;
                if enum_matches && variant == vv {
                    // Both have no payload
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    // Pattern has payload patterns, value has payload
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        if patterns.len() == 1 {
                            // Single payload - match directly
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)? {
                                return Ok(true);
                            }
                        } else {
                            // Multiple payload patterns - payload should be a tuple
                            if let Value::Tuple(values) = vp.as_ref() {
                                if patterns.len() == values.len() {
                                    let mut all_match = true;
                                    for (pat, val) in patterns.iter().zip(values.iter()) {
                                        if !pattern_matches(pat, val, bindings, enums)? {
                                            all_match = false;
                                            break;
                                        }
                                    }
                                    if all_match {
                                        return Ok(true);
                                    }
                                }
                            }
                        }
                    }
                    // Pattern has no payload but value does - match any payload
                    if payload.is_none() && value_payload.is_some() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        Pattern::Tuple(patterns) => match_sequence_pattern(value, patterns, bindings, enums, true),
        Pattern::Array(patterns) => match_sequence_pattern(value, patterns, bindings, enums, false),

        Pattern::Struct { name, fields } => {
            if let Value::Object {
                class,
                fields: obj_fields,
            } = value
            {
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
                Type::Union(types) => types.iter().any(|t| {
                    if let Type::Simple(name) = t {
                        value.matches_type(name)
                    } else {
                        true
                    }
                }),
                _ => true,
            };

            if type_matches {
                pattern_matches(pattern, value, bindings, enums)
            } else {
                Ok(false)
            }
        }

        Pattern::Range { start, end, inclusive } => {
            // Range patterns only work with integers
            let Value::Int(val) = value else {
                return Ok(false);
            };
            // Evaluate start and end expressions (must be integer literals)
            let start_val = match start.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            let end_val = match end.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            // Check if value is in range
            if *inclusive {
                Ok(*val >= start_val && *val <= end_val)
            } else {
                Ok(*val >= start_val && *val < end_val)
            }
        }

        Pattern::Rest => Ok(true),
    }
}

/// Extract the covered variant name from a pattern (for exhaustiveness checking).
/// Returns Some(variant_name) for enum patterns, None for wildcards/catch-all.
fn extract_covered_variant(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Enum { variant, .. } => Some(variant.clone()),
        Pattern::Or(patterns) => {
            // Or patterns cover all their sub-patterns
            // Return the first one for simplicity (all should be checked)
            patterns.first().and_then(extract_covered_variant)
        }
        Pattern::Typed { pattern, .. } => extract_covered_variant(pattern),
        // Wildcard, Identifier, etc. are catch-all - they cover everything
        _ => None,
    }
}

/// Collect all variant names covered by a list of match arm patterns.
/// Returns (covered_variants, has_catch_all).
pub(crate) fn collect_covered_variants(patterns: &[&Pattern]) -> (Vec<String>, bool) {
    let mut covered = Vec::new();
    let mut has_catch_all = false;

    for pattern in patterns {
        if is_catch_all_pattern(pattern) {
            has_catch_all = true;
        } else if let Some(variant) = extract_covered_variant(pattern) {
            if !covered.contains(&variant) {
                covered.push(variant);
            }
        }
        // For Or patterns, collect all sub-variants
        if let Pattern::Or(sub_patterns) = pattern {
            for sub_pat in sub_patterns {
                if let Some(variant) = extract_covered_variant(sub_pat) {
                    if !covered.contains(&variant) {
                        covered.push(variant);
                    }
                }
            }
        }
    }

    (covered, has_catch_all)
}

/// Check if a match expression covers all variants of an enum.
/// Returns None if exhaustive, Some(missing_variants) otherwise.
pub(crate) fn check_enum_exhaustiveness(
    enum_name: &str,
    arm_patterns: &[&Pattern],
    enums: &Enums,
) -> Option<Vec<String>> {
    // Get the enum definition from module-level or block-scoped enums
    let enum_def = enums
        .get(enum_name)
        .cloned()
        .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()))?;

    // Get all variant names from the enum definition
    let all_variants: Vec<String> = enum_def.variants.iter().map(|v| v.name.clone()).collect();

    // Collect covered variants from patterns
    let (covered, has_catch_all) = collect_covered_variants(arm_patterns);

    // If there's a catch-all, all variants are covered
    if has_catch_all {
        return None;
    }

    // Find missing variants
    let missing: Vec<String> = all_variants.into_iter().filter(|v| !covered.contains(v)).collect();

    if missing.is_empty() {
        None
    } else {
        Some(missing)
    }
}
