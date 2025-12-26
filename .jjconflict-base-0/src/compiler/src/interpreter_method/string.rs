// String method implementations for the interpreter
//
// This module contains all built-in methods for String values (str type):
// - Basic operations: len, char_count, is_empty, chars, bytes
// - Searching: contains, starts_with, ends_with, find, index_of, rfind
// - Case conversion: to_upper, to_lower, trim variants
// - Manipulation: reversed, sorted, take, drop, append, prepend, push, pop, clear
// - Slicing: split, split_lines, slice, substring, replace
// - Parsing: parse_int, parse_float, to_int, to_float
// - Padding: pad_left, pad_right
// - Type checking: is_numeric, is_alpha, is_alphanumeric, is_whitespace

// Built-in methods for String
if let Value::Str(ref s) = recv_val {
    match method {
        "len" => return Ok(Value::Int(s.len() as i64)),
        "char_count" => return Ok(Value::Int(s.chars().count() as i64)),
        "is_empty" => return Ok(Value::Bool(s.is_empty())),
        "chars" => {
            let chars: Vec<Value> = s.chars().map(|c| Value::Str(c.to_string())).collect();
            return Ok(Value::Array(chars));
        }
        "bytes" => {
            let bytes: Vec<Value> = s.bytes().map(|b| Value::Int(b as i64)).collect();
            return Ok(Value::Array(bytes));
        }
        "contains" => {
            let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.contains(&needle)));
        }
        "starts_with" => {
            let prefix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.starts_with(&prefix)));
        }
        "ends_with" => {
            let suffix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.ends_with(&suffix)));
        }
        "find_str" | "find" | "index_of" => {
            let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(match s.find(&needle) {
                Some(idx) => Value::some(Value::Int(idx as i64)),
                None => Value::none(),
            });
        }
        "to_upper" | "to_uppercase" => return Ok(Value::Str(s.to_uppercase())),
        "to_lower" | "to_lowercase" => return Ok(Value::Str(s.to_lowercase())),
        "trim" | "trimmed" => return Ok(Value::Str(s.trim().to_string())),
        "trim_start" | "trim_left" => return Ok(Value::Str(s.trim_start().to_string())),
        "trim_end" | "trim_right" => return Ok(Value::Str(s.trim_end().to_string())),
        "reversed" => return Ok(Value::Str(s.chars().rev().collect())),
        "sorted" => {
            let mut chars: Vec<char> = s.chars().collect();
            chars.sort();
            return Ok(Value::Str(chars.into_iter().collect()));
        }
        "taken" | "take" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            return Ok(Value::Str(s.chars().take(n).collect()));
        }
        "dropped" | "drop" | "skip" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            return Ok(Value::Str(s.chars().skip(n).collect()));
        }
        "appended" => {
            let ch = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(format!("{}{}", s, ch)));
        }
        "prepended" => {
            let ch = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(format!("{}{}", ch, s)));
        }
        "push" => {
            // Note: Returns a new string with the character appended (strings are immutable)
            let ch = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(format!("{}{}", s, ch)));
        }
        "push_str" => {
            // Note: Returns a new string with the string appended (strings are immutable)
            let other = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(format!("{}{}", s, other)));
        }
        "pop" => {
            // Note: Returns Some(last_char) but doesn't modify the string (immutable)
            if s.is_empty() {
                return Ok(Value::none());
            }
            let last = s.chars().last().map(|c| Value::Str(c.to_string())).unwrap_or(Value::Nil);
            return Ok(Value::some(last));
        }
        "clear" => {
            // Note: Returns empty string (strings are immutable)
            return Ok(Value::Str(String::new()));
        }
        "split" => {
            let sep = eval_arg(args, 0, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?.to_key_string();
            let parts: Vec<Value> = s.split(&sep).map(|p| Value::Str(p.to_string())).collect();
            return Ok(Value::Array(parts));
        }
        "split_lines" | "lines" => {
            let parts: Vec<Value> = s.lines().map(|p| Value::Str(p.to_string())).collect();
            return Ok(Value::Array(parts));
        }
        "replace" => {
            let old = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            let new = eval_arg(args, 1, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(s.replace(&old, &new)));
        }
        "replace_first" => {
            let old = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            let new = eval_arg(args, 1, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(s.replacen(&old, &new, 1)));
        }
        "slice" | "substring" => {
            let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let end = args.get(1)
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.as_int().unwrap_or(s.len() as i64) as usize)
                .unwrap_or(s.len());
            // Work with char indices for unicode safety
            let chars: Vec<char> = s.chars().collect();
            let end = end.min(chars.len());
            let start = start.min(end);
            let result: String = chars[start..end].iter().collect();
            return Ok(Value::Str(result));
        }
        "repeat" => {
            let n = eval_arg_usize(args, 0, 1, env, functions, classes, enums, impl_methods)?;
            return Ok(Value::Str(s.repeat(n)));
        }
        "reverse" => {
            return Ok(Value::Str(s.chars().rev().collect()));
        }
        "last_index_of" | "rfind" => {
            let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            match s.rfind(&needle) {
                Some(idx) => return Ok(Value::Int(idx as i64)),
                None => return Ok(Value::Int(-1)),
            }
        }
        "parse_int" => {
            match s.trim().parse::<i64>() {
                Ok(n) => return Ok(Value::some(Value::Int(n))),
                Err(_) => return Ok(Value::none()),
            }
        }
        "parse_float" => {
            match s.trim().parse::<f64>() {
                Ok(n) => return Ok(Value::some(Value::Float(n))),
                Err(_) => return Ok(Value::none()),
            }
        }
        "to_int" => {
            match s.trim().parse::<i64>() {
                Ok(n) => return Ok(Value::Int(n)),
                Err(_) => return Ok(Value::Int(0)),
            }
        }
        "to_float" => {
            match s.trim().parse::<f64>() {
                Ok(n) => return Ok(Value::Float(n)),
                Err(_) => return Ok(Value::Float(0.0)),
            }
        }
        "char_at" | "at" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            match s.chars().nth(idx) {
                Some(c) => return Ok(Value::Str(c.to_string())),
                None => return Ok(Value::Nil),
            }
        }
        "pad_left" | "pad_start" => {
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let pad_char = eval_arg(args, 1, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?
                .to_key_string()
                .chars()
                .next()
                .unwrap_or(' ');
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::Str(s.clone()));
            }
            let padding: String = std::iter::repeat(pad_char).take(width - current_len).collect();
            return Ok(Value::Str(format!("{}{}", padding, s)));
        }
        "pad_right" | "pad_end" => {
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let pad_char = eval_arg(args, 1, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?
                .to_key_string()
                .chars()
                .next()
                .unwrap_or(' ');
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::Str(s.clone()));
            }
            let padding: String = std::iter::repeat(pad_char).take(width - current_len).collect();
            return Ok(Value::Str(format!("{}{}", s, padding)));
        }
        "is_numeric" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_ascii_digit())));
        }
        "is_alpha" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphabetic())));
        }
        "is_alphanumeric" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphanumeric())));
        }
        "is_whitespace" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_whitespace())));
        }
        "count" => {
            let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Int(s.matches(&needle).count() as i64));
        }
        _ => {}
    }
}
