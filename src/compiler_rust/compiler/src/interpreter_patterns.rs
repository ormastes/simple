// ORCHESTRATOR NOTE: the killed agent ALSO modified interpreter_control.rs (callers updated to a 5-arg match_pattern-style signature). That partial is saved at /tmp/a3_partial_interpreter_control.rs; the repo copy was reset to upstream. If you change the fn signature in interpreter_patterns.rs you must update those callers too.
//! Pattern matching functions for the interpreter
//!
//! This module provides pattern matching implementations used by match expressions
//! and other pattern-based constructs.

use std::collections::HashMap;

use crate::error::CompileError;
use crate::value::Value;
use simple_parser::ast::{Expr, FStringPart, Pattern, Type};

use super::{Classes, Enums, BLOCK_SCOPED_ENUMS};

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
    classes: &Classes,
    is_tuple: bool,
) -> Result<bool, CompileError> {
    let values: &[Value] = if is_tuple {
        if let Value::Tuple(vals) = value {
            vals.as_slice()
        } else {
            return Ok(false);
        }
    } else if let Value::Array(vals) = value {
        vals.as_slice()
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
            if !pattern_matches(pat, val, bindings, enums, classes)? {
                return Ok(false);
            }
        }

        // Match patterns after rest (from the end)
        for (i, pat) in after_rest.iter().enumerate() {
            let val_idx = values.len() - after_rest.len() + i;
            if !pattern_matches(pat, &values[val_idx], bindings, enums, classes)? {
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
        bindings.insert("__rest__".to_string(), Value::array(rest_values));

        Ok(true)
    } else {
        // No rest pattern - exact match required
        if patterns.len() != values.len() {
            return Ok(false);
        }

        for (pat, val) in patterns.iter().zip(values.iter()) {
            if !pattern_matches(pat, val, bindings, enums, classes)? {
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
    classes: &Classes,
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
                            FStringPart::Literal(s) => pattern_str.push_str(s),
                            FStringPart::Expr(_) | FStringPart::ExprWithFormat(_, _) => {
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
                Expr::Nil => Ok(matches!(value, Value::Nil)
                    || matches!(value, Value::Enum { ref variant, .. } if variant == "None")),
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
                // When pattern has enum_name="_", match any enum with the correct variant.
                // Also treat "Option" and "Result" as wildcards: the parser hardcodes
                // `case Some(...)` → Pattern::Enum{name:"Option"} and `case Ok/Err(...)` →
                // Pattern::Enum{name:"Result"}, so user-defined enums with variants named
                // Some/None/Ok/Err would otherwise fail to match. The variant name check
                // on line 245 prevents cross-variant leakage.
                let enum_matches =
                    enum_name == "_" || enum_name == ve || matches!(enum_name.as_str(), "Option" | "Result");
                if enum_matches && variant == vv {
                    // Both have no payload
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    // Pattern has payload patterns, value has payload
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        if patterns.len() == 1 {
                            // Single payload - match directly
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums, classes)? {
                                return Ok(true);
                            }
                        } else {
                            // Multiple payload patterns - payload should be a tuple
                            if let Value::Tuple(values) = vp.as_ref() {
                                if patterns.len() == values.len() {
                                    let mut all_match = true;
                                    for (pat, val) in patterns.iter().zip(values.iter()) {
                                        if !pattern_matches(pat, val, bindings, enums, classes)? {
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

            // Positional class/struct pattern: `case ClassName(a, b, c)` where the value is
            // a class instance (`Value::Object`).  The parser emits this as
            // `Pattern::Enum { name: "_", variant: "ClassName", payload: Some([…]) }` because
            // it cannot distinguish enum variants from class names at parse time.
            //
            // When `name == "_"` (user-defined, unresolved) and `variant` matches the object's
            // class name, bind the payload patterns to the class fields in declaration order.
            // This is the correct semantics: positional patterns follow the field order in the
            // class definition.
            if let Value::Object { class, fields: obj_fields } = value {
                let name_matches = enum_name == "_"
                    || enum_name == class
                    || matches!(enum_name.as_str(), "Option" | "Result");
                if name_matches && variant == class {
                    match payload {
                        None => {
                            // Unit pattern `case Foo:` — matches any instance of Foo
                            return Ok(true);
                        }
                        Some(patterns) => {
                            // Positional: look up field order from ClassDef
                            if let Some(class_def) = classes.get(class.as_str()) {
                                let field_names: Vec<&str> =
                                    class_def.fields.iter().map(|f| f.name.as_str()).collect();
                                if patterns.len() != field_names.len() {
                                    // Arity mismatch — clean failure (not an error, just no-match)
                                    return Ok(false);
                                }
                                let mut temp_bindings = HashMap::new();
                                let mut all_match = true;
                                for (pat, field_name) in patterns.iter().zip(field_names.iter()) {
                                    if let Some(field_val) = obj_fields.get(*field_name) {
                                        if !pattern_matches(pat, field_val, &mut temp_bindings, enums, classes)? {
                                            all_match = false;
                                            break;
                                        }
                                    } else {
                                        all_match = false;
                                        break;
                                    }
                                }
                                if all_match {
                                    bindings.extend(temp_bindings);
                                    return Ok(true);
                                }
                            }
                            // ClassDef not found — fall through to Ok(false)
                        }
                    }
                }
            }

            Ok(false)
        }

        Pattern::Tuple(patterns) => match_sequence_pattern(value, patterns, bindings, enums, classes, true),
        Pattern::Array(patterns) => match_sequence_pattern(value, patterns, bindings, enums, classes, false),

        Pattern::Struct { name, fields } => {
            if let Value::Object {
                class,
                fields: obj_fields,
            } = value
            {
                if class == name {
                    if std::env::var("SIMPLE_DEBUG_MATCH").as_deref() == Ok("1") {
                        eprintln!("[DEBUG Pattern::Struct] class={} obj_fields={:?}", class, obj_fields.keys().collect::<Vec<_>>());
                        for (k, v) in obj_fields.iter() {
                            eprintln!("  field {} = {:?}", k, v);
                        }
                    }
                    for (field_name, field_pat) in fields {
                        if let Some(field_val) = obj_fields.get(field_name) {
                            if !pattern_matches(field_pat, field_val, bindings, enums, classes)? {
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
                if pattern_matches(pat, value, &mut temp_bindings, enums, classes)? {
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
                pattern_matches(pattern, value, bindings, enums, classes)
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

#[cfg(test)]
mod tests {
    use simple_parser::Parser;
    use crate::interpreter::evaluate_module;

    /// Run a Simple snippet and return the exit code.
    /// Use `main = <expr>` to set a numeric exit code (0 = ok, non-zero = error).
    fn run(src: &str) -> i32 {
        let mut parser = Parser::new(src);
        let module = parser.parse().expect("parse");
        evaluate_module(&module.items).expect("evaluate")
    }

    // --- Positional class pattern (the bug) ---

    #[test]
    fn positional_class_3field_matches_and_binds() {
        // Regression for: case P(x, y, z) over a class instance silently no-matched.
        // The match arm should fire and each binding should carry the correct field value.
        let src = r#"
class P:
    x: i64
    y: i64
    z: i64

var result_ = -1
val p = P(x: 10, y: 20, z: 30)
match p:
    case P(a, b, c):
        if a == 10 and b == 20 and c == 30:
            result_ = 0
        else:
            result_ = 2
    case _:
        result_ = 1
main = result_
"#;
        let code = run(src);
        assert_eq!(code, 0, "3-field positional class match should fire and bind correctly");
    }

    #[test]
    fn positional_class_20field_matches() {
        // Wide destructure (20 fields) — the production case from flat_ast_bridge_part1.spl.
        let src = r#"
class Big:
    f1: i64
    f2: i64
    f3: i64
    f4: i64
    f5: i64
    f6: i64
    f7: i64
    f8: i64
    f9: i64
    f10: i64
    f11: i64
    f12: i64
    f13: i64
    f14: i64
    f15: i64
    f16: i64
    f17: i64
    f18: i64
    f19: i64
    f20: i64

var result_ = -1
val b = Big(f1: 1, f2: 2, f3: 3, f4: 4, f5: 5, f6: 6, f7: 7, f8: 8, f9: 9, f10: 10, f11: 11, f12: 12, f13: 13, f14: 14, f15: 15, f16: 16, f17: 17, f18: 18, f19: 19, f20: 20)
match b:
    case Big(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20):
        if a1 == 1 and a20 == 20:
            result_ = 0
        else:
            result_ = 2
    case _:
        result_ = 1
main = result_
"#;
        let code = run(src);
        assert_eq!(code, 0, "20-field positional class match should fire and bind in declaration order");
    }

    #[test]
    fn positional_class_arity_mismatch_does_not_match() {
        // Arity mismatch: 2 patterns for a 3-field class → clean no-match, not a panic.
        let src = r#"
class P:
    x: i64
    y: i64
    z: i64

var result_ = -1
val p = P(x: 1, y: 2, z: 3)
match p:
    case P(a, b):
        result_ = 1
    case _:
        result_ = 0
main = result_
"#;
        let code = run(src);
        assert_eq!(code, 0, "arity mismatch should produce clean no-match (fall through to wildcard)");
    }

    #[test]
    fn named_field_struct_pattern_still_works() {
        // Named-field patterns (Pattern::Struct via `{ }` brace syntax) must be unaffected.
        let src = r#"
class P:
    x: i64
    y: i64

var result_ = -1
val p = P(x: 5, y: 6)
match p:
    case P { x, y }:
        if x == 5 and y == 6:
            result_ = 0
        else:
            result_ = 2
    case _:
        result_ = 1
main = result_
"#;
        let code = run(src);
        assert_eq!(code, 0, "named-field struct pattern must still work after positional class fix");
    }

    #[test]
    fn enum_positional_pattern_unaffected() {
        // Enum variant positional patterns must continue to work.
        let src = r#"
enum Color:
    Red
    Green
    Blue(i64)

var result_ = -1
val c = Color.Blue(42)
match c:
    case Color.Blue(n):
        if n == 42:
            result_ = 0
        else:
            result_ = 2
    case _:
        result_ = 1
main = result_
"#;
        let code = run(src);
        assert_eq!(code, 0, "enum positional pattern must be unaffected by the class fix");
    }
}
