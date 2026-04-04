use std::collections::HashMap;
use std::sync::Arc;

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
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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
                let mut local_env: Env = Env::new();
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
                        let mut local_env: Env = Env::new();

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
                    FStringPart::Literal(lit) => out.push_str(lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        let display = try_call_fmt_method(&v, env, functions, classes, enums, impl_methods)
                            .unwrap_or_else(|| v.to_display_string());
                        out.push_str(&display);
                    }
                    FStringPart::ExprWithFormat(e, spec) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        let display = format_value_with_spec_interp(&v, spec);
                        out.push_str(&display);
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
                        FStringPart::ExprWithFormat(e, spec) => {
                            if let Expr::Identifier(id) = e {
                                default_template.push_str(&format!("{{{}:{}}}", id, spec));
                            } else {
                                let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                                let formatted = format_value_with_spec_interp(&v, spec);
                                default_template.push_str(&formatted);
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
            // Evaluate the block using the appropriate handler, passing env for variable access
            match blocks::evaluate_block_with_env(kind, payload, env) {
                Ok(value) => Ok(Some(value)),
                Err(e) => Err(e),
            }
        }
        Expr::Identifier(name) => {
            // Handle pass_todo, pass_do_nothing, pass_dn as no-op identifiers
            if name == "pass_todo" || name == "pass_do_nothing" || name == "pass_dn" {
                return Ok(Some(Value::Nil));
            }
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
                    def: func,
                    captured_env: Arc::new(Env::new()), // Top-level functions don't capture
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

/// Format a Value using a Python-style format specifier (interpreter mode).
///
/// Supports: `.Nf` (float precision), `0Nd` (zero-padded int), `>N`/`<N`/`^N` (alignment),
/// `.N%` (percentage), `x`/`X` (hex), `o` (octal), `b` (binary), `e`/`E` (scientific).
fn format_value_with_spec_interp(v: &Value, spec: &str) -> String {
    let chars: Vec<char> = spec.chars().collect();
    let len = chars.len();
    if len == 0 {
        return v.to_display_string();
    }

    // Parse format spec: [[fill]align][sign][#][0][width][grouping][.precision][type]
    let mut pos = 0;
    let mut fill = ' ';
    let mut align = '\0';
    let mut _sign = '\0';
    let mut alt_form = false;
    let mut zero_pad = false;
    let mut width: Option<usize> = None;
    let mut _grouping = '\0';
    let mut precision: Option<usize> = None;
    let mut type_code = '\0';

    // [fill]align
    if len >= 2 && matches!(chars[1], '<' | '>' | '^' | '=') {
        fill = chars[0];
        align = chars[1];
        pos = 2;
    } else if len >= 1 && matches!(chars[0], '<' | '>' | '^' | '=') {
        align = chars[0];
        pos = 1;
    }

    // Sign
    if pos < len && matches!(chars[pos], '+' | '-' | ' ') {
        _sign = chars[pos];
        pos += 1;
    }

    // Alt form '#'
    if pos < len && chars[pos] == '#' {
        alt_form = true;
        pos += 1;
    }

    // Zero pad
    if pos < len && chars[pos] == '0' {
        zero_pad = true;
        pos += 1;
    }

    // Width
    let width_start = pos;
    while pos < len && chars[pos].is_ascii_digit() {
        pos += 1;
    }
    if pos > width_start {
        let w: String = chars[width_start..pos].iter().collect();
        width = w.parse().ok();
    }

    // Grouping
    if pos < len && matches!(chars[pos], ',' | '_') {
        _grouping = chars[pos];
        pos += 1;
    }

    // Precision
    if pos < len && chars[pos] == '.' {
        pos += 1;
        let prec_start = pos;
        while pos < len && chars[pos].is_ascii_digit() {
            pos += 1;
        }
        if pos > prec_start {
            let p: String = chars[prec_start..pos].iter().collect();
            precision = p.parse().ok();
        } else {
            precision = Some(0);
        }
    }

    // Type code
    if pos < len {
        type_code = chars[pos];
    }

    // Format the raw value
    let raw = match type_code {
        'f' | 'F' => {
            let f = match v {
                Value::Float(f) => *f,
                Value::Int(i) => *i as f64,
                _ => v.to_display_string().parse::<f64>().unwrap_or(0.0),
            };
            let prec = precision.unwrap_or(6);
            format!("{:.prec$}", f, prec = prec)
        }
        'e' | 'E' => {
            let f = match v {
                Value::Float(f) => *f,
                Value::Int(i) => *i as f64,
                _ => v.to_display_string().parse::<f64>().unwrap_or(0.0),
            };
            let prec = precision.unwrap_or(6);
            if type_code == 'E' {
                format!("{:.prec$E}", f, prec = prec)
            } else {
                format!("{:.prec$e}", f, prec = prec)
            }
        }
        'd' => {
            let i = match v {
                Value::Int(i) => *i,
                Value::Float(f) => *f as i64,
                _ => v.to_display_string().parse::<i64>().unwrap_or(0),
            };
            format!("{}", i)
        }
        'x' | 'X' => {
            let i = match v {
                Value::Int(i) => *i,
                _ => v.to_display_string().parse::<i64>().unwrap_or(0),
            };
            let result = if type_code == 'X' {
                format!("{:X}", i)
            } else {
                format!("{:x}", i)
            };
            if alt_form {
                let prefix = if type_code == 'X' { "0X" } else { "0x" };
                format!("{}{}", prefix, result)
            } else {
                result
            }
        }
        'o' => {
            let i = match v {
                Value::Int(i) => *i,
                _ => v.to_display_string().parse::<i64>().unwrap_or(0),
            };
            let result = format!("{:o}", i);
            if alt_form { format!("0o{}", result) } else { result }
        }
        'b' => {
            let i = match v {
                Value::Int(i) => *i,
                _ => v.to_display_string().parse::<i64>().unwrap_or(0),
            };
            let result = format!("{:b}", i);
            if alt_form { format!("0b{}", result) } else { result }
        }
        '%' => {
            let f = match v {
                Value::Float(f) => *f,
                Value::Int(i) => *i as f64,
                _ => v.to_display_string().parse::<f64>().unwrap_or(0.0),
            };
            let prec = precision.unwrap_or(6);
            format!("{:.prec$}%", f * 100.0, prec = prec)
        }
        _ => {
            // Default: string representation, with precision as max length
            let s = v.to_display_string();
            if let Some(prec) = precision {
                if s.len() > prec { s[..prec].to_string() } else { s }
            } else {
                s
            }
        }
    };

    // Apply width/alignment
    if let Some(w) = width {
        let current_len = raw.chars().count();
        if current_len < w {
            let padding = w - current_len;
            let fill_char = if zero_pad && align == '\0' { '0' } else { fill };
            let effective_align = if align != '\0' {
                align
            } else if zero_pad {
                '>'
            } else {
                '<'
            };
            match effective_align {
                '>' => {
                    let pad: String = std::iter::repeat(fill_char).take(padding).collect();
                    if fill_char == '0' && (raw.starts_with('+') || raw.starts_with('-')) {
                        let (sign, rest) = raw.split_at(1);
                        format!("{}{}{}", sign, pad, rest)
                    } else {
                        format!("{}{}", pad, raw)
                    }
                }
                '<' => {
                    let pad: String = std::iter::repeat(fill_char).take(padding).collect();
                    format!("{}{}", raw, pad)
                }
                '^' => {
                    let left_pad = padding / 2;
                    let right_pad = padding - left_pad;
                    let left: String = std::iter::repeat(fill_char).take(left_pad).collect();
                    let right: String = std::iter::repeat(fill_char).take(right_pad).collect();
                    format!("{}{}{}", left, raw, right)
                }
                '=' => {
                    let pad: String = std::iter::repeat(fill_char).take(padding).collect();
                    if raw.starts_with('+') || raw.starts_with('-') {
                        let (sign, rest) = raw.split_at(1);
                        format!("{}{}{}", sign, pad, rest)
                    } else {
                        format!("{}{}", pad, raw)
                    }
                }
                _ => raw,
            }
        } else {
            raw
        }
    } else {
        raw
    }
}

/// Try calling the `fmt()` method on a value if it's an Object with that method.
/// Returns Some(string) if fmt() exists and returns a string, None otherwise.
fn try_call_fmt_method(
    value: &Value,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Option<String> {
    use super::super::interpreter_control::call_method_if_exists;
    if let Value::Object { .. } = value {
        if let Ok(Some(result)) = call_method_if_exists(value, "fmt", &[], env, functions, classes, enums, impl_methods)
        {
            if let Value::Str(s) = result {
                return Some(s);
            }
            return Some(result.to_display_string());
        }
    }
    None
}

/// Try calling the `debug_fmt()` method on a value if it's an Object with that method.
/// Returns Some(string) if debug_fmt() exists, None otherwise.
pub(crate) fn try_call_debug_fmt_method(
    value: &Value,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Option<String> {
    use super::super::interpreter_control::call_method_if_exists;
    if let Value::Object { .. } = value {
        if let Ok(Some(result)) =
            call_method_if_exists(value, "debug_fmt", &[], env, functions, classes, enums, impl_methods)
        {
            if let Value::Str(s) = result {
                return Some(s);
            }
            return Some(result.to_display_string());
        }
    }
    None
}
