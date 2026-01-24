// String method implementations for the interpreter
//
// This module contains all built-in methods for String values (str type):
// - Basic operations: len, char_count, is_empty, chars, bytes
// - Searching: contains, starts_with, ends_with, find, index_of, rfind, find_all
// - Case conversion: to_upper, to_lower, capitalize, swapcase, title
// - Trimming: trim, strip, trim_start, trim_end, chomp
// - Prefix/Suffix: removeprefix, removesuffix
// - Manipulation: reversed, sorted, take, drop, append, prepend, push, pop, clear, squeeze
// - Slicing: split, split_lines, slice, substring, substr, replace, partition, rpartition
// - Joining: join (join array with string as delimiter)
// - Parsing: parse_int, parse_float, to_int, to_float
// - Padding: pad_left, pad_right, center, zfill
// - Type checking: is_numeric, is_alpha, is_alphanumeric, is_whitespace
// - Character codes: ord, codepoint (returns Unicode code point of first char)

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
        "has" | "contains" => {
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
        "up" | "upper" | "to_upper" | "to_uppercase" => return Ok(Value::Str(s.to_uppercase())),
        "down" | "lower" | "to_lower" | "to_lowercase" => return Ok(Value::Str(s.to_lowercase())),
        "capitalize" => {
            // Uppercase first character, lowercase the rest
            let mut chars = s.chars();
            match chars.next() {
                None => return Ok(Value::Str(String::new())),
                Some(first) => {
                    let rest: String = chars.map(|c| c.to_lowercase().to_string()).collect::<String>();
                    return Ok(Value::Str(format!("{}{}", first.to_uppercase(), rest)));
                }
            }
        }
        "swapcase" => {
            // Swap case of all characters
            let result: String = s.chars().map(|c| {
                if c.is_uppercase() {
                    c.to_lowercase().to_string()
                } else {
                    c.to_uppercase().to_string()
                }
            }).collect();
            return Ok(Value::Str(result));
        }
        "title" | "titlecase" => {
            // Titlecase: uppercase first character of each word
            let mut result = String::new();
            let mut capitalize_next = true;
            for c in s.chars() {
                if c.is_whitespace() || c.is_ascii_punctuation() {
                    result.push(c);
                    capitalize_next = true;
                } else if capitalize_next {
                    result.push_str(&c.to_uppercase().to_string());
                    capitalize_next = false;
                } else {
                    result.push_str(&c.to_lowercase().to_string());
                }
            }
            return Ok(Value::Str(result));
        }
        "trim" | "trimmed" | "strip" => return Ok(Value::Str(s.trim().to_string())),
        "trim_start" | "trim_left" => return Ok(Value::Str(s.trim_start().to_string())),
        "trim_end" | "trim_right" => return Ok(Value::Str(s.trim_end().to_string())),
        "removeprefix" | "remove_prefix" => {
            // Remove prefix if present
            let prefix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(s.strip_prefix(&prefix).unwrap_or(s).to_string()));
        }
        "removesuffix" | "remove_suffix" => {
            // Remove suffix if present
            let suffix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Str(s.strip_suffix(&suffix).unwrap_or(s).to_string()));
        }
        "chomp" => {
            // Remove trailing newline or record separator (default: \n, \r\n, \r)
            let result = s.strip_suffix("\r\n")
                .or_else(|| s.strip_suffix('\n'))
                .or_else(|| s.strip_suffix('\r'))
                .unwrap_or(s);
            return Ok(Value::Str(result.to_string()));
        }
        "squeeze" => {
            // Remove duplicate adjacent characters
            // If no argument, squeeze all duplicates. If argument provided, only squeeze those chars
            let chars_to_squeeze = args.get(0)
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.to_key_string());

            if s.is_empty() {
                return Ok(Value::Str(String::new()));
            }

            let mut result = String::new();
            let mut prev: Option<char> = None;

            for c in s.chars() {
                let should_check = match &chars_to_squeeze {
                    Some(set) => set.contains(c),
                    None => true,
                };

                if should_check {
                    if Some(c) != prev {
                        result.push(c);
                    }
                } else {
                    result.push(c);
                }
                prev = Some(c);
            }
            return Ok(Value::Str(result));
        }
        "rev" | "reversed" => return Ok(Value::Str(s.chars().rev().collect())),
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
        "partition" => {
            // Split into [before, separator, after] at first occurrence
            let sep = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if sep.is_empty() {
                return Ok(Value::Array(vec![
                    Value::Str(s.clone()),
                    Value::Str(String::new()),
                    Value::Str(String::new()),
                ]));
            }
            match s.find(&sep) {
                Some(idx) => {
                    let before = &s[..idx];
                    let after = &s[idx + sep.len()..];
                    return Ok(Value::Array(vec![
                        Value::Str(before.to_string()),
                        Value::Str(sep),
                        Value::Str(after.to_string()),
                    ]));
                }
                None => {
                    return Ok(Value::Array(vec![
                        Value::Str(s.clone()),
                        Value::Str(String::new()),
                        Value::Str(String::new()),
                    ]));
                }
            }
        }
        "rpartition" => {
            // Split into [before, separator, after] at last occurrence
            let sep = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if sep.is_empty() {
                return Ok(Value::Array(vec![
                    Value::Str(String::new()),
                    Value::Str(String::new()),
                    Value::Str(s.clone()),
                ]));
            }
            match s.rfind(&sep) {
                Some(idx) => {
                    let before = &s[..idx];
                    let after = &s[idx + sep.len()..];
                    return Ok(Value::Array(vec![
                        Value::Str(before.to_string()),
                        Value::Str(sep),
                        Value::Str(after.to_string()),
                    ]));
                }
                None => {
                    return Ok(Value::Array(vec![
                        Value::Str(String::new()),
                        Value::Str(String::new()),
                        Value::Str(s.clone()),
                    ]));
                }
            }
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
        "rev" | "reverse" => {
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
        "ord" | "codepoint" => {
            // Return the Unicode code point of the first character
            match s.chars().next() {
                Some(c) => return Ok(Value::Int(c as i64)),
                None => return Ok(Value::Int(0)),
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
        "center" => {
            // Center string with padding on both sides
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
            let total_padding = width - current_len;
            let left_padding = total_padding / 2;
            let right_padding = total_padding - left_padding;
            let left: String = std::iter::repeat(pad_char).take(left_padding).collect();
            let right: String = std::iter::repeat(pad_char).take(right_padding).collect();
            return Ok(Value::Str(format!("{}{}{}", left, s, right)));
        }
        "zfill" => {
            // Pad with zeros on the left to reach specified width
            // Handles sign correctly for numeric strings
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::Str(s.clone()));
            }

            // Check if string starts with + or -
            let (sign, rest) = if s.starts_with('+') || s.starts_with('-') {
                (&s[0..1], &s[1..])
            } else {
                ("", s.as_str())
            };

            let padding: String = "0".repeat(width - current_len);
            return Ok(Value::Str(format!("{}{}{}", sign, padding, rest)));
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
        "substr" => {
            // substr(start, length) - Extract substring by start position and length
            // Unlike substring(start, end), this uses length
            let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let length = eval_arg_usize(args, 1, s.len(), env, functions, classes, enums, impl_methods)?;
            // Work with char indices for unicode safety
            let chars: Vec<char> = s.chars().collect();
            let start = start.min(chars.len());
            let end = (start + length).min(chars.len());
            let result: String = chars[start..end].iter().collect();
            return Ok(Value::Str(result));
        }
        "find_all" | "find_indices" => {
            // find_all(needle) - Return all indices where needle is found
            let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if needle.is_empty() {
                return Ok(Value::Array(vec![]));
            }
            let indices: Vec<Value> = s.match_indices(&needle)
                .map(|(idx, _)| Value::Int(idx as i64))
                .collect();
            return Ok(Value::Array(indices));
        }
        "join" => {
            // join(array) - Join array elements with this string as delimiter
            // Example: ",".join(["a", "b", "c"]) -> "a,b,c"
            let arr_val = eval_arg(args, 0, Value::Array(vec![]), env, functions, classes, enums, impl_methods)?;
            if let Value::Array(arr) = arr_val {
                let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
                return Ok(Value::Str(parts.join(s)));
            } else {
                return Err(crate::error::CompileError::semantic(
                    "join expects an array argument",
                ));
            }
        }
        "with" => {
            // FString.with method: replace placeholders {key} with values from dict
            // Example: "Hello {name}".with {"name": "Alice"} -> "Hello Alice"
            let dict_val = eval_arg(
                args,
                0,
                Value::Dict(std::collections::HashMap::new()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            if let Value::Dict(data) = dict_val {
                let mut result = s.clone();
                for (key, value) in &data {
                    let placeholder = format!("{{{}}}", key);
                    let replacement = value.to_display_string();
                    result = result.replace(&placeholder, &replacement);
                }
                return Ok(Value::Str(result));
            } else {
                return Err(crate::error::CompileError::semantic(
                    "FString.with expects a dict argument",
                ));
            }
        }
        _ => {}
    }
}
