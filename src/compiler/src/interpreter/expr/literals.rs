use std::collections::HashMap;

use simple_parser::ast::{Expr, FStringPart};
use simple_parser::token::NumericSuffix;

use super::evaluate_expr;
use super::units::{lookup_unit_family, lookup_unit_family_with_si};
use crate::blocks;
use crate::error::CompileError;
use crate::value::{OptionVariant, Value};

use super::super::{ClassDef, Enums, Env, FunctionDef, ImplMethods, MODULE_GLOBALS, MOVED_VARS};

pub(super) fn eval_literal_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(Some(Value::Int(*value))),
        Expr::TypedInteger(value, suffix) => Ok(Some(match suffix {
            NumericSuffix::Unit(unit_name) => {
                // Create a Unit value for unit-suffixed integers
                // Look up family from thread-local registry, with SI prefix support
                let (family, si_multiplier, _base_suffix) = lookup_unit_family_with_si(unit_name);
                // Apply SI prefix multiplier if present
                let final_value = if let Some(mult) = si_multiplier {
                    // Convert to float and apply multiplier
                    Value::Float(*value as f64 * mult)
                } else {
                    Value::Int(*value)
                };
                Value::Unit {
                    value: Box::new(final_value),
                    suffix: unit_name.clone(),
                    family,
                }
            }
            _ => Value::Int(*value),
        })),
        Expr::Float(value) => Ok(Some(Value::Float(*value))),
        Expr::TypedFloat(value, suffix) => Ok(Some(match suffix {
            NumericSuffix::Unit(unit_name) => {
                // Create a Unit value for unit-suffixed floats, with SI prefix support
                let (family, si_multiplier, _base_suffix) = lookup_unit_family_with_si(unit_name);
                // Apply SI prefix multiplier if present
                let final_value = if let Some(mult) = si_multiplier {
                    *value * mult
                } else {
                    *value
                };
                Value::Unit {
                    value: Box::new(Value::Float(final_value)),
                    suffix: unit_name.clone(),
                    family,
                }
            }
            _ => Value::Float(*value),
        })),
        Expr::Bool(b) => Ok(Some(Value::Bool(*b))),
        Expr::Nil => Ok(Some(Value::Nil)),
        Expr::String(s) => Ok(Some(Value::Str(s.clone()))),
        Expr::TypedString(s, suffix) => {
            // Create a Unit value for unit-suffixed strings (e.g., "127.0.0.1"_ip)
            let family = lookup_unit_family(suffix);
            Ok(Some(Value::Unit {
                value: Box::new(Value::Str(s.clone())),
                suffix: suffix.clone(),
                family,
            }))
        }
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
            Ok(Some(Value::Str(out)))
        }
        Expr::Symbol(s) => Ok(Some(Value::Symbol(s.clone()))),
        // Custom block expressions: m{...}, sh{...}, sql{...}, re{...}, etc.
        Expr::BlockExpr { kind, payload } => {
            // Evaluate the block using the appropriate handler
            match blocks::evaluate_block(kind, payload) {
                Ok(value) => Ok(Some(value)),
                Err(e) => Err(e),
            }
        }
        Expr::Identifier(name) => {
            // Check for Option::None literal using type-safe variant
            if name == OptionVariant::None.as_str() {
                return Ok(Some(Value::none()));
            }
            // Check if this variable has been moved (unique pointer move semantics)
            let is_moved = MOVED_VARS.with(|cell| cell.borrow().contains(name));
            if is_moved {
                return Err(CompileError::Semantic(format!(
                    "use of moved value: '{}'. Unique pointers can only be used once.",
                    name
                )));
            }
            // First check env for local variables and closures
            if let Some(val) = env.get(name) {
                return Ok(Some(val.clone()));
            }
            // Then check functions for top-level function definitions
            // Return as Value::Function for first-class function usage
            if let Some(func) = functions.get(name).cloned() {
                return Ok(Some(Value::Function {
                    name: name.clone(),
                    def: Box::new(func.clone()),
                    captured_env: Env::new(), // Top-level functions don't capture
                }));
            }
            // Check classes - return as Constructor for constructor polymorphism
            if classes.contains_key(name) {
                return Ok(Some(Value::Constructor {
                    class_name: name.clone(),
                }));
            }
            // Check enums - return as EnumType for variant construction (EnumName.Variant)
            if enums.contains_key(name) {
                return Ok(Some(Value::EnumType {
                    enum_name: name.clone(),
                }));
            }
            // Check module-level globals (for functions accessing module-level let mut variables)
            let global_val = MODULE_GLOBALS.with(|cell| cell.borrow().get(name).cloned());
            if let Some(val) = global_val {
                return Ok(Some(val));
            }
            // Collect all known names for typo suggestion
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut msg = format!("undefined variable: {name}");
            if let Some(suggestion) = crate::error::typo::format_suggestion(name, known_names) {
                msg.push_str(&format!("; {}", suggestion));
            }
            Err(CompileError::Semantic(msg))
        }
        _ => Ok(None),
    }
}
