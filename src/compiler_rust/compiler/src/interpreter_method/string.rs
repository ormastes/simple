// String method implementations for the interpreter
//
// This module contains all built-in methods for String values (str type):
// - Basic operations: len, char_count, is_empty, chars, bytes
// - Searching: contains, starts_with, ends_with, find, index_of, rfind, find_all
// - Case conversion: to_upper, to_lower, capitalize, swapcase, title
// - Trimming: trim, strip, trim_start, trim_end, trim_start_matches, trim_end_matches, chomp
// - Prefix/Suffix: removeprefix, removesuffix
// - Manipulation: reversed, sorted, take, drop, append, prepend, push, pop, clear, squeeze
// - Slicing: split, split_lines, slice, substring, substr, replace, partition, rpartition
// - Joining: join (join array with string as delimiter)
// - Parsing: parse_int (+ parse_i32, parse_i64), parse_float, to_int, to_float
// - Padding: pad_left, pad_right, center, zfill
// - Type checking: is_numeric, is_alpha, is_alphanumeric, is_whitespace
// - Character codes: ord, codepoint (returns Unicode code point of first char)

// Built-in methods for String
if let Value::Str(ref s) = recv_val {
    match method {
        "to_string" | "to_text" => return Ok(Value::shared_text(s.clone())),
        "len" | "length" => return Ok(Value::Int(s.len() as i64)),
        "char_count" => return Ok(Value::Int(s.chars().count() as i64)),
        "is_empty" => return Ok(Value::Bool(s.is_empty())),
        "chars" => {
            let chars: Vec<Value> = s.chars().map(|c| Value::text(c.to_string())).collect();
            return Ok(Value::array(chars));
        }
        "bytes" => {
            let bytes: Vec<Value> = s.bytes().map(|b| Value::Int(b as i64)).collect();
            return Ok(Value::array(bytes));
        }
        "has" | "contains" => {
            let needle = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.contains(&needle)));
        }
        "starts_with" => {
            let prefix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.starts_with(&prefix)));
        }
        "ends_with" => {
            let suffix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::Bool(s.ends_with(&suffix)));
        }
        "find_str" | "find" | "index_of" => {
            let needle = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            // Two-arg `index_of(needle, start)`: byte-offset search from
            // `start`, mirroring `rt_text_find` exactly so the interpreter and
            // the compiled lane agree: start < 0 clamps to 0; empty needle
            // returns min(start, len); start past the end returns -1;
            // byte-indexed result, -1 for not-found. Scoped to `index_of`
            // only — `find`/`find_str` keep their one-arg contract (extra
            // args were and remain ignored) because the compiled lane lowers
            // only two-arg `index_of`, and a wider interpreter would silently
            // diverge from it.
            if method == "index_of" && args.len() >= 2 {
                let start_raw = eval_arg_int(args, 1, 0, env, functions, classes, enums, impl_methods)?;
                let start = start_raw.max(0) as usize;
                let bytes = s.as_bytes();
                let nb = needle.as_bytes();
                if nb.is_empty() {
                    return Ok(Value::Int(start.min(bytes.len()) as i64));
                }
                if start >= bytes.len() {
                    return Ok(Value::Int(-1));
                }
                return Ok(match bytes[start..].windows(nb.len()).position(|w| w == nb) {
                    Some(idx) => Value::Int((start + idx) as i64),
                    None => Value::Int(-1),
                });
            }
            return Ok(match s.find(&needle) {
                Some(idx) => Value::Int(idx as i64),
                None => Value::Int(-1),
            });
        }
        "up" | "upper" | "uppercase" | "to_upper" | "to_uppercase" => return Ok(Value::text(s.to_uppercase())),
        "down" | "lower" | "lowercase" | "to_lower" | "to_lowercase" => return Ok(Value::text(s.to_lowercase())),
        "capitalize" => {
            // Uppercase first character, lowercase the rest
            let mut chars = s.chars();
            match chars.next() {
                None => return Ok(Value::text(String::new())),
                Some(first) => {
                    let rest: String = chars.map(|c| c.to_lowercase().to_string()).collect::<String>();
                    return Ok(Value::text(format!("{}{}", first.to_uppercase(), rest)));
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
            return Ok(Value::text(result));
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
            return Ok(Value::text(result));
        }
        "trim" | "trimmed" | "strip" => return Ok(Value::text(s.trim().to_string())),
        "trim_start" | "trim_left" => return Ok(Value::text(s.trim_start().to_string())),
        "trim_end" | "trim_right" => return Ok(Value::text(s.trim_end().to_string())),
        "trim_start_matches" => {
            // Repeatedly remove prefix until it no longer matches
            let prefix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.trim_start_matches(&*prefix).to_string()));
        }
        "trim_end_matches" => {
            // Repeatedly remove suffix until it no longer matches
            let suffix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.trim_end_matches(&*suffix).to_string()));
        }
        "removeprefix" | "remove_prefix" => {
            // Remove prefix if present
            let prefix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.strip_prefix(&prefix).unwrap_or(s).to_string()));
        }
        "removesuffix" | "remove_suffix" => {
            // Remove suffix if present
            let suffix = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.strip_suffix(&suffix).unwrap_or(s).to_string()));
        }
        "chomp" => {
            // Remove trailing newline or record separator (default: \n, \r\n, \r)
            let result = s.strip_suffix("\r\n")
                .or_else(|| s.strip_suffix('\n'))
                .or_else(|| s.strip_suffix('\r'))
                .unwrap_or(s);
            return Ok(Value::text(result.to_string()));
        }
        "squeeze" => {
            // Remove duplicate adjacent characters
            // If no argument, squeeze all duplicates. If argument provided, only squeeze those chars
            let chars_to_squeeze = args.first()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.to_key_string());

            if s.is_empty() {
                return Ok(Value::text(String::new()));
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
            return Ok(Value::text(result));
        }
        "rev" | "reversed" => return Ok(Value::text(s.chars().rev().collect::<String>())),
        "sorted" => {
            let mut chars: Vec<char> = s.chars().collect();
            chars.sort();
            return Ok(Value::text(chars.into_iter().collect::<String>()));
        }
        "taken" | "take" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            return Ok(Value::text(s.chars().take(n).collect::<String>()));
        }
        "dropped" | "drop" | "skip" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            return Ok(Value::text(s.chars().skip(n).collect::<String>()));
        }
        "appended" => {
            let ch = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(format!("{}{}", s, ch)));
        }
        "prepended" => {
            let ch = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(format!("{}{}", ch, s)));
        }
        "push" => {
            // Note: Returns a new string with the character appended (strings are immutable)
            let ch = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(format!("{}{}", s, ch)));
        }
        "push_str" => {
            // Note: Returns a new string with the string appended (strings are immutable)
            let other = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(format!("{}{}", s, other)));
        }
        "pop" => {
            // Returns the LAST CHARACTER, and does not modify the string
            // (strings are immutable — see the `push` note above).
            //
            // This used to return `Some(last_char)`. It was the only `pop` in
            // the language that returned an Option: measured on BOTH engines,
            // `[1, 2, 3].pop()` evaluates to the bare element `3`, never
            // `Some(3)`. Text was the outlier, and the Option wrapping could
            // not be matched by any compiled lane — the JIT has no Option
            // constructor for text (`Some("c")` renders as an opaque
            // `<enum@0x...>` there, and a `text?` value renders bare), so the
            // wrapping was permanently unreachable outside this interpreter.
            // An empty text has no last character, so it yields the empty text
            // — unambiguous, since no real character is ever the empty text.
            if s.is_empty() {
                return Ok(Value::text(String::new()));
            }
            let last = s.chars().last().map(|c| c.to_string()).unwrap_or_default();
            return Ok(Value::text(last));
        }
        "clear" => {
            // Note: Returns empty string (strings are immutable)
            return Ok(Value::text(String::new()));
        }
        "split" => {
            let sep = eval_arg(args, 0, Value::text(" "), env, functions, classes, enums, impl_methods)?.to_key_string();
            let limit = if args.len() > 1 {
                eval_arg(args, 1, Value::Int(0), env, functions, classes, enums, impl_methods)?.as_int().unwrap_or(0)
            } else {
                0
            };
            let raw_parts: Vec<String> = if limit > 0 && sep.is_empty() {
                let chars: Vec<char> = s.chars().collect();
                if limit == 1 {
                    vec![s.to_string()]
                } else {
                    let head = ((limit - 1) as usize).min(chars.len());
                    let mut bounded: Vec<String> = chars[..head].iter().map(char::to_string).collect();
                    bounded.push(chars[head..].iter().collect());
                    bounded
                }
            } else if limit > 0 {
                s.splitn(limit as usize, &sep).map(str::to_string).collect()
            } else {
                s.split(&sep).map(str::to_string).collect()
            };
            let parts: Vec<Value> = raw_parts.into_iter().map(Value::text).collect();
            return Ok(Value::array(parts));
        }
        "split_lines" | "lines" => {
            let parts: Vec<Value> = s.lines().map(|p| Value::text(p.to_string())).collect();
            return Ok(Value::array(parts));
        }
        "partition" => {
            // Split into [before, separator, after] at first occurrence
            let sep = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if sep.is_empty() {
                return Ok(Value::array(vec![
                    Value::shared_text(s.clone()),
                    Value::text(String::new()),
                    Value::text(String::new()),
                ]));
            }
            match s.find(&sep) {
                Some(idx) => {
                    let before = &s[..idx];
                    let after = &s[idx + sep.len()..];
                    return Ok(Value::array(vec![
                        Value::text(before.to_string()),
                        Value::text(sep),
                        Value::text(after.to_string()),
                    ]));
                }
                None => {
                    return Ok(Value::array(vec![
                        Value::shared_text(s.clone()),
                        Value::text(String::new()),
                        Value::text(String::new()),
                    ]));
                }
            }
        }
        "rpartition" => {
            // Split into [before, separator, after] at last occurrence
            let sep = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if sep.is_empty() {
                return Ok(Value::array(vec![
                    Value::text(String::new()),
                    Value::text(String::new()),
                    Value::shared_text(s.clone()),
                ]));
            }
            match s.rfind(&sep) {
                Some(idx) => {
                    let before = &s[..idx];
                    let after = &s[idx + sep.len()..];
                    return Ok(Value::array(vec![
                        Value::text(before.to_string()),
                        Value::text(sep),
                        Value::text(after.to_string()),
                    ]));
                }
                None => {
                    return Ok(Value::array(vec![
                        Value::text(String::new()),
                        Value::text(String::new()),
                        Value::shared_text(s.clone()),
                    ]));
                }
            }
        }
        "replace" => {
            let old = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            let new = eval_arg(args, 1, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.replace(&old, &new)));
        }
        "replace_first" => {
            let old = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            let new = eval_arg(args, 1, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(Value::text(s.replacen(&old, &new, 1)));
        }
        "slice" | "substring" => {
            let start_raw = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let end_raw = args.get(1)
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.as_int().unwrap_or(s.len() as i64))
                .unwrap_or(s.len() as i64);
            let start = start_raw.max(0) as usize;
            let end = end_raw.max(0) as usize;
            // Identity fast path: full-string slice avoids the chars() walk + Vec<char>.
            // Byte-len upper-bounds char count, so end >= s.len() guarantees end >= chars().count().
            if start == 0 && end >= s.len() {
                return Ok(Value::shared_text(s.clone()));
            }
            // BYTE-indexed, matching the JIT/native lane (`rt_slice`, which
            // slices `s->data + begin` raw) and this interpreter's own
            // byte-valued `len` / `index_of`. Indexing by character here made
            // an index produced by `len`/`index_of` invalid input to `slice`:
            // for "caféZdef" (9 bytes / 8 chars) `index_of("Z")` is 5, and a
            // char-indexed `slice(0, 5)` wrongly yielded "caféZ".
            let bytes = s.as_bytes();
            let end = end.min(bytes.len());
            let start = start.min(end);
            // A range that splits a multi-byte codepoint cannot be held in
            // Rust's UTF-8 `String`; preserve the RAW bytes (`Value::StrBytes`)
            // exactly like the bracket-slice path in
            // `interpreter/expr/collections.rs` and like the JIT/native lane's
            // `rt_slice`, which slices `s->data + begin` raw. The previous
            // `String::from_utf8_lossy` here substituted U+FFFD, which is
            // valid-but-wrong: it CHANGES the byte length of the result
            // (`"aé€𝄞z".slice(0, 2).len()` was 4, not 2) and makes the original
            // byte unrecoverable at concat time. That was the sole remaining
            // interpret-vs-jit divergence in
            // `test/fixtures/engine_differential/utf8_slice_boundary.spl`.
            // UTF-8 slice audit, stage 1 (COUNTING ONLY, default off). Measured
            // on the RAW range, which is now also what is returned.
            if simple_runtime::text_slice_audit::enabled() {
                simple_runtime::text_slice_audit::note(
                    simple_runtime::text_slice_audit::site::INTERP_METHOD,
                    start as i64,
                    end as i64,
                    bytes,
                    &bytes[start..end],
                );
            }
            return Ok(Value::text_from_bytes(bytes[start..end].to_vec()));
        }
        "repeat" => {
            // Read the count as a SIGNED integer and clamp. `eval_arg_usize`
            // casts with `as usize`, so `"x".repeat(-2)` became a count of
            // 18446744073709551614 and the interpreter PANICKED with
            // "capacity overflow" instead of returning a value. Non-positive
            // counts yield the empty string, matching the pure-Simple
            // `str_repeat` (src/lib/common/string_core.spl) and
            // `rt_string_repeat` in both runtimes.
            let n = eval_arg_int(args, 0, 1, env, functions, classes, enums, impl_methods)?;
            if n <= 0 {
                return Ok(Value::text(String::new()));
            }
            return Ok(Value::text(s.repeat(n as usize)));
        }
        "rev" | "reverse" => {
            return Ok(Value::text(s.chars().rev().collect::<String>()));
        }
        "last_index_of" | "rfind" => {
            let needle = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            return Ok(match s.rfind(&needle) {
                Some(idx) => Value::Int(idx as i64),
                None => Value::Int(-1),
            });
        }
        "parse_int" | "parse_i32" | "parse_i64" => {
            match s.trim().parse::<i64>() {
                Ok(n) => return Ok(Value::some(Value::Int(n))),
                Err(_) => return Ok(Value::none()),
            }
        }
        "parse_float" | "parse_f64" | "parse_f64_safe" => {
            match s.trim().parse::<f64>() {
                Ok(n) => return Ok(Value::some(Value::Float(n))),
                Err(_) => return Ok(Value::none()),
            }
        }
        "to_int" | "to_i64" | "to_i32" | "to_i16" | "to_i8" => {
            match s.trim().parse::<i64>() {
                Ok(n) => return Ok(Value::Int(n)),
                Err(_) => return Ok(Value::Int(0)),
            }
        }
        "to_float" | "to_f64" | "to_f32" => {
            match s.trim().parse::<f64>() {
                Ok(n) => return Ok(Value::Float(n)),
                Err(_) => return Ok(Value::Float(0.0)),
            }
        }
        "char_at" | "at" => {
            let raw_idx = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            if raw_idx < 0 {
                return Ok(Value::text(String::new()));
            }
            let idx = raw_idx as usize;
            match s.chars().nth(idx) {
                Some(c) => return Ok(Value::text(c.to_string())),
                None => return Ok(Value::text(String::new())),
            }
        }
        "ord" | "codepoint" | "code_point" => {
            // Return the Unicode code point of the first character
            match s.chars().next() {
                Some(c) => return Ok(Value::Int(c as i64)),
                None => return Ok(Value::Int(0)),
            }
        }
        "char_code_at" => {
            // Return the Unicode code point of the character at the given index.
            //
            // SEMANTICS ARE UNCHANGED: `idx` is a CHARACTER (codepoint) index.
            // Only the cost changed. `s.chars().nth(idx)` walked from byte 0 on
            // every call -- O(idx) -- which made every
            // `while i < s.len(): s.char_code_at(i)` loop O(n^2). Inside an
            // ASCII prefix a character index IS a byte index, so answer straight
            // out of the buffer; fall back to the original walk otherwise.
            // A negative index is OUT OF RANGE, not index 0. `eval_arg_usize`
            // saturates negatives to 0, which is right for the count/width
            // callers it was written for but wrong for an index accessor: it
            // made `"abc".char_code_at(-1)` return 97, a REAL codepoint, where
            // the compiled lane returns 0. Guarded the same way as `char_at`
            // above and as the native impl (`runtime_native.c`:
            // `if (index < 0) return 0;`), so all engines agree.
            let raw_idx = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            if raw_idx < 0 {
                return Ok(Value::Int(0));
            }
            let idx = raw_idx as usize;
            let bytes = s.as_bytes();
            if shared_text_is_ascii(s) {
                return Ok(Value::Int(bytes.get(idx).map_or(0, |b| *b as i64)));
            }
            if first_non_ascii(bytes) > idx {
                // `idx` lies strictly inside the ASCII prefix.
                return Ok(Value::Int(bytes[idx] as i64));
            }
            match s.chars().nth(idx) {
                Some(c) => return Ok(Value::Int(c as i64)),
                None => return Ok(Value::Int(0)),
            }
        }
        "byte_at" => {
            // Return the raw BYTE at the given BYTE index.
            //
            // Deliberately NOT `char_code_at`: that one is CHARACTER-indexed and
            // the two disagree on any non-ASCII text (`"café,".byte_at(3)` is
            // 195, the 0xC3 lead byte, while `char_code_at(3)` is 233 for 'é').
            // Byte-framing callers -- `browser_renderer_protocol.spl` scanning
            // for 10 `\n` / 44 `,` and then `.to_u8()`-ing the result -- index
            // the byte stream `text_to_bytes` produces, so a character index
            // would desync the frame the moment a multi-byte codepoint appeared
            // in a payload.
            //
            // Out-of-range yields 0, matching `char_code_at`'s convention.
            //
            // A NEGATIVE index is out of range too, so it must also yield 0.
            // Reading it through `eval_arg_usize` saturated negatives to 0 and
            // returned a REAL byte -- `"abc".byte_at(-1)` was 97 -- diverging
            // from the native impl (`runtime_native.c`: `if (index < 0)
            // return 0;`) and silently turning a bad index into plausible data.
            let raw_idx = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            if raw_idx < 0 {
                return Ok(Value::Int(0));
            }
            let idx = raw_idx as usize;
            return Ok(Value::Int(s.as_bytes().get(idx).map_or(0, |b| *b as i64)));
        }
        "pad_left" | "pad_start" => {
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let pad_char = eval_arg(args, 1, Value::text(" "), env, functions, classes, enums, impl_methods)?
                .to_key_string()
                .chars()
                .next()
                .unwrap_or(' ');
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::shared_text(s.clone()));
            }
            let padding: String = std::iter::repeat_n(pad_char, width - current_len).collect();
            return Ok(Value::text(format!("{}{}", padding, s)));
        }
        "pad_right" | "pad_end" => {
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let pad_char = eval_arg(args, 1, Value::text(" "), env, functions, classes, enums, impl_methods)?
                .to_key_string()
                .chars()
                .next()
                .unwrap_or(' ');
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::shared_text(s.clone()));
            }
            let padding: String = std::iter::repeat_n(pad_char, width - current_len).collect();
            return Ok(Value::text(format!("{}{}", s, padding)));
        }
        "center" => {
            // Center string with padding on both sides
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let pad_char = eval_arg(args, 1, Value::text(" "), env, functions, classes, enums, impl_methods)?
                .to_key_string()
                .chars()
                .next()
                .unwrap_or(' ');
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::shared_text(s.clone()));
            }
            let total_padding = width - current_len;
            let left_padding = total_padding / 2;
            let right_padding = total_padding - left_padding;
            let left: String = std::iter::repeat_n(pad_char, left_padding).collect();
            let right: String = std::iter::repeat_n(pad_char, right_padding).collect();
            return Ok(Value::text(format!("{}{}{}", left, s, right)));
        }
        "zfill" => {
            // Pad with zeros on the left to reach specified width
            // Handles sign correctly for numeric strings
            let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let current_len = s.chars().count();
            if current_len >= width {
                return Ok(Value::shared_text(s.clone()));
            }

            // Check if string starts with + or -
            let (sign, rest) = if s.starts_with('+') || s.starts_with('-') {
                (&s[0..1], &s[1..])
            } else {
                ("", s.as_str())
            };

            let padding: String = "0".repeat(width - current_len);
            return Ok(Value::text(format!("{}{}{}", sign, padding, rest)));
        }
        "is_numeric" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_ascii_digit())));
        }
        "is_alpha" | "is_alphabetic" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphabetic())));
        }
        "is_digit" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_ascii_digit())));
        }
        "is_alphanumeric" | "is_alnum" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphanumeric())));
        }
        "is_whitespace" => {
            return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_whitespace())));
        }
        "count" => {
            let needle = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
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
            return Ok(Value::text(result));
        }
        "find_all" | "find_indices" => {
            // find_all(needle) - Return all indices where needle is found
            let needle = eval_arg(args, 0, Value::text(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
            if needle.is_empty() {
                return Ok(Value::array(vec![]));
            }
            let indices: Vec<Value> = s.match_indices(&needle)
                .map(|(idx, _)| Value::Int(idx as i64))
                .collect();
            return Ok(Value::array(indices));
        }
        "join" => {
            // join(array) - Join array elements with this string as delimiter
            // Example: ",".join(["a", "b", "c"]) -> "a,b,c"
            let arr_val = eval_arg(args, 0, Value::array(vec![]), env, functions, classes, enums, impl_methods)?;
            if let Value::Array(arr) = arr_val {
                let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
                return Ok(Value::text(parts.join(s)));
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
                Value::Dict(std::sync::Arc::new(std::collections::HashMap::new())),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            if let Value::Dict(data) = dict_val {
                let mut result = s.as_ref().clone();
                for (key, value) in data.iter() {
                    let placeholder = format!("{{{}}}", key);
                    let replacement = value.to_display_string();
                    result = result.replace(&placeholder, &replacement);
                }
                return Ok(Value::text(result));
            } else {
                return Err(crate::error::CompileError::semantic(
                    "FString.with expects a dict argument",
                ));
            }
        }
        "ptr" => {
            // Return raw pointer to string's bytes as i64 (for SFFI/codegen)
            // We must pin the string so the pointer remains valid after this Value is dropped.
            // PINNED_STRINGS is defined at module level in mod.rs so it can be cleared externally.
            let cloned = s.to_string();
            let ptr = PINNED_STRINGS.with(|cell| {
                let mut cache = cell.borrow_mut();
                cache.push(cloned);
                cache.last().unwrap().as_ptr() as i64
            });
            return Ok(Value::Int(ptr));
        }
        _ => {}
    }
}
