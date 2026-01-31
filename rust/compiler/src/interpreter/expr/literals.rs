use std::collections::HashMap;

use simple_parser::ast::{Expr, FStringPart};
use simple_parser::token::NumericSuffix;

use super::evaluate_expr;
use super::units::{lookup_unit_family, lookup_unit_family_with_si, suffix_to_type_names};
use crate::blocks;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{OptionVariant, Value};
use super::super::interpreter_state::{LITERAL_FUNCTIONS, LiteralFunctionInfo};
use crate::interpreter::block_exec::exec_block_fn;
use crate::interpreter::core_types::Control;

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
            // Custom string literal suffix handling:
            // 1. Check LITERAL_FUNCTIONS registry for explicit override
            // 2. Convert suffix to type names and look up in classes
            // 3. Call Type.from(value) if found
            // 4. Fall back to Value::Unit if nothing found

            // Step 1: Check for explicit literal fn override
            let literal_fn_result: Option<LiteralFunctionInfo> =
                LITERAL_FUNCTIONS.with(|cell| cell.borrow().get(suffix).cloned());

            if let Some(lit_fn_info) = literal_fn_result {
                // Execute the literal function body with the string value
                let mut local_env: HashMap<String, Value> = HashMap::new();
                local_env.insert(lit_fn_info.param_name.clone(), Value::Str(s.clone()));

                match exec_block_fn(
                    &lit_fn_info.body,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                ) {
                    Ok((Control::Return(v), _)) => return Ok(Some(v)),
                    Ok((_, Some(implicit_val))) => return Ok(Some(implicit_val)),
                    Ok((_, None)) => return Ok(Some(Value::Nil)),
                    Err(e) => return Err(e),
                }
            }

            // Step 2: Convert suffix to type names and look for matching class
            let type_names = suffix_to_type_names(suffix);
            for type_name in &type_names {
                if let Some(class_def) = classes.get(type_name).cloned() {
                    // Step 3: Look for static `from` method (or `from_raw` for raw strings)
                    // TypedString comes from double-quoted strings, so use `from`
                    if let Some(from_method) = class_def.methods.iter().find(|m| m.name == "from") {
                        // Execute the from method with the string value
                        let mut local_env: HashMap<String, Value> = HashMap::new();

                        // Bind the string value to the first parameter
                        if !from_method.params.is_empty() {
                            let param_name = &from_method.params[0].name;
                            local_env.insert(param_name.clone(), Value::Str(s.clone()));
                        }

                        match exec_block_fn(
                            &from_method.body,
                            &mut local_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok((Control::Return(v), _)) => return Ok(Some(v)),
                            Ok((_, Some(implicit_val))) => return Ok(Some(implicit_val)),
                            Ok((_, None)) => return Ok(Some(Value::Nil)),
                            Err(e) => return Err(e),
                        }
                    }
                }
            }

            // Step 4: Fall back to Value::Unit (backward compatibility)
            let family = lookup_unit_family(suffix);
            Ok(Some(Value::Unit {
                value: Box::new(Value::Str(s.clone())),
                suffix: suffix.clone(),
                family,
            }))
        }
        Expr::FString { parts, .. } => {
            let mut out = String::new();
            for part in parts {
                match part {
                    FStringPart::Literal(lit) => out.push_str(&lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(&e, env, functions, classes, enums, impl_methods)?;
                        out.push_str(&v.to_display_string());
                    }
                }
            }
            Ok(Some(Value::Str(out)))
        }
        Expr::Symbol(s) => Ok(Some(Value::Symbol(s.clone()))),

        // i18n string literals
        Expr::I18nString { name, default_text } => {
            // Look up in locale registry, fallback to default text
            let text = crate::i18n::lookup(name).unwrap_or_else(|| default_text.clone());
            Ok(Some(Value::Str(text)))
        }

        // i18n template strings
        Expr::I18nTemplate { name, parts, args } => {
            // Try to look up the template in the locale registry first
            let template = if let Some(localized) = crate::i18n::lookup(name) {
                // Use the localized template
                localized
            } else {
                // Build the default template from parts
                let mut default_template = String::new();
                for part in parts {
                    match part {
                        FStringPart::Literal(lit) => default_template.push_str(lit),
                        FStringPart::Expr(e) => {
                            // Record placeholder for substitution
                            if let Expr::Identifier(id) = e {
                                default_template.push_str(&format!("{{{}}}", id));
                            } else {
                                // For complex expressions, evaluate inline
                                let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                                default_template.push_str(&v.to_display_string());
                            }
                        }
                    }
                }
                default_template
            };

            // Substitute the args into the template
            let mut result = template;
            for (key, value_expr) in args {
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                result = result.replace(&format!("{{{}}}", key), &value.to_display_string());
            }

            Ok(Some(Value::Str(result)))
        }

        // i18n reference (named string without inline default)
        Expr::I18nRef(name) => {
            // Look up in locale registry, return placeholder if not found
            let text = crate::i18n::lookup_or_placeholder(name);
            Ok(Some(Value::Str(text)))
        }

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
                let ctx = ErrorContext::new()
                    .with_code(codes::USE_AFTER_FREE)
                    .with_help("unique pointers can only be used once; the value has already been moved");
                return Err(CompileError::semantic_with_context(
                    format!("use of moved value: '{}'. Unique pointers can only be used once.", name),
                    ctx,
                ));
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
            // E1001 - Undefined Variable
            let suggestion = crate::error::typo::suggest_name(name, known_names.clone());
            let mut ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_VARIABLE)
                .with_help("check that the variable is defined and in scope");

            if let Some(best_match) = suggestion {
                ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
            }

            if !known_names.is_empty() && known_names.len() <= 5 {
                let names_list = known_names.join(", ");
                ctx = ctx.with_note(format!("available variables: {}", names_list));
            }

            Err(CompileError::semantic_with_context(
                format!("variable `{}` not found", name),
                ctx,
            ))
        }
        _ => Ok(None),
    }
}
