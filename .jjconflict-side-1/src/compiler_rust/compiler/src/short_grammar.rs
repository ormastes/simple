//! Shared short-grammar suggestions for diagnostics and LSP.

use regex::Regex;
use std::sync::OnceLock;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShortGrammarSuggestion {
    pub line: usize,
    pub column: usize,
    pub end_column: usize,
    pub replacement: String,
    pub message: String,
}

fn callback_regex() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| {
        Regex::new(r#"\.(map|filter|any|all|then)\(\\([A-Za-z][A-Za-z0-9_]*):\s*"#)
            .expect("short grammar callback regex")
    })
}

fn method_ref_regex(param: &str) -> Regex {
    Regex::new(&format!(
        r#"^\s*{}\.(?P<method>[A-Za-z_][A-Za-z0-9_]*)\(\)\s*$"#,
        regex::escape(param)
    ))
    .expect("method ref regex")
}

fn plain_identifier_regex(param: &str) -> Regex {
    Regex::new(&format!(r#"\b{}\b"#, regex::escape(param))).expect("identifier regex")
}

fn is_readable_short_candidate(expr: &str) -> bool {
    let trimmed = expr.trim();
    !trimmed.is_empty()
        && trimmed.len() <= 80
        && !trimmed.contains('\\')
        && !trimmed.contains("match ")
        && !trimmed.contains(" if ")
        && !trimmed.contains(";")
        && !has_assignment_like_operator(trimmed)
}

fn has_assignment_like_operator(expr: &str) -> bool {
    let bytes = expr.as_bytes();
    let mut in_string = false;
    let mut escaped = false;
    let mut idx = 0;
    while idx < bytes.len() {
        let ch = bytes[idx] as char;
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            idx += 1;
            continue;
        }
        if ch == '"' {
            in_string = true;
        } else if ch == '=' {
            let prev = idx.checked_sub(1).map(|i| bytes[i] as char);
            let next = bytes.get(idx + 1).map(|b| *b as char);
            if prev != Some('=') && prev != Some('!') && prev != Some('<') && prev != Some('>') && next != Some('=') {
                return true;
            }
        }
        idx += 1;
    }
    false
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn replace_identifier_outside_strings(body: &str, param: &str, replacement: &str) -> (String, bool) {
    let bytes = body.as_bytes();
    let param_bytes = param.as_bytes();
    let mut out = String::with_capacity(body.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut changed = false;
    let mut idx = 0;
    while idx < bytes.len() {
        let ch = bytes[idx] as char;
        if in_string {
            out.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            idx += 1;
            continue;
        }

        if ch == '"' {
            in_string = true;
            out.push(ch);
            idx += 1;
            continue;
        }

        let matches = idx + param_bytes.len() <= bytes.len()
            && &bytes[idx..idx + param_bytes.len()] == param_bytes
            && idx.checked_sub(1).map_or(true, |i| !is_identifier_byte(bytes[i]))
            && bytes
                .get(idx + param_bytes.len())
                .map_or(true, |b| !is_identifier_byte(*b));
        if matches {
            out.push_str(replacement);
            idx += param_bytes.len();
            changed = true;
        } else {
            out.push(ch);
            idx += 1;
        }
    }
    (out, changed)
}

fn is_code_position(line: &str, position: usize) -> bool {
    let bytes = line.as_bytes();
    let mut in_string = false;
    let mut escaped = false;
    let mut idx = 0;
    while idx < position && idx < bytes.len() {
        let ch = bytes[idx] as char;
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            idx += 1;
            continue;
        }
        if ch == '"' {
            in_string = true;
        } else if ch == '#' {
            return false;
        }
        idx += 1;
    }
    !in_string
}

fn replacement_for(param: &str, body: &str) -> Option<String> {
    let body = body.trim();
    if !is_readable_short_candidate(body) {
        return None;
    }

    let (placeholder_body, has_param) = replace_identifier_outside_strings(body, param, "_1");
    if !has_param {
        return Some(format!("\\_: {}", body));
    }

    if let Some(captures) = method_ref_regex(param).captures(body) {
        if let Some(method) = captures.name("method") {
            return Some(format!("&:{}", method.as_str()));
        }
    }

    Some(placeholder_body)
}

fn find_callback_end(line: &str, body_start: usize) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut idx = body_start;
    while idx < bytes.len() {
        let ch = bytes[idx] as char;
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            idx += 1;
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' => {
                if depth == 0 {
                    return Some(idx);
                }
                depth -= 1;
            }
            ']' | '}' => {
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

pub fn collect_short_grammar_suggestions(source: &str) -> Vec<ShortGrammarSuggestion> {
    let mut suggestions = Vec::new();
    let re = callback_regex();
    for (line_idx, line) in source.lines().enumerate() {
        let trimmed = line.trim_start();
        if trimmed.starts_with('#') || trimmed.starts_with("\"\"\"") {
            continue;
        }
        for captures in re.captures_iter(line) {
            let Some(full) = captures.get(0) else { continue };
            if !is_code_position(line, full.start()) {
                continue;
            }
            let Some(param) = captures.get(2) else { continue };
            let body_start = full.end();
            let Some(body_end) = find_callback_end(line, body_start) else {
                continue;
            };
            let body = &line[body_start..body_end];
            let Some(replacement) = replacement_for(param.as_str(), body) else {
                continue;
            };

            let lambda_offset = full.start() + full.as_str().find('\\').unwrap_or(0);
            suggestions.push(ShortGrammarSuggestion {
                line: line_idx + 1,
                column: lambda_offset + 1,
                end_column: body_end + 1,
                message: format!("use short grammar `{}` for this readable callback", replacement),
                replacement,
            });
        }
    }
    suggestions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suggests_placeholder_callback() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val doubled = nums.map(\\x: x * 2)\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "_1 * 2");
    }

    #[test]
    fn suggests_method_reference_callback() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val lengths = words.map(\\w: w.len())\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "&:len");
    }

    #[test]
    fn suggests_wildcard_callback_for_constants() {
        let suggestions =
            collect_short_grammar_suggestions("fn f():\n    val separators = headers.map(\\h: \"---\")\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "\\_: \"---\"");
    }

    #[test]
    fn ignores_existing_wildcard_callbacks() {
        let suggestions =
            collect_short_grammar_suggestions("fn f():\n    val separators = headers.map(\\_: \"---\")\n");
        assert!(suggestions.is_empty());
    }

    #[test]
    fn suggests_equality_predicate() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val matches = nums.filter(\\x: x == 2)\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "_1 == 2");
    }

    #[test]
    fn ignores_assignment_like_callback() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val updated = nums.map(\\x: x = 2)\n");
        assert!(suggestions.is_empty());
    }

    #[test]
    fn does_not_rewrite_identifier_inside_string_literal() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val names = nums.map(\\x: \"x\" + x)\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "\"x\" + _1");
    }

    #[test]
    fn ignores_callbacks_inside_comments_and_strings() {
        let suggestions = collect_short_grammar_suggestions(
            "fn f():\n    val text = \".map(\\x: x * 2)\"\n    # nums.map(\\x: x * 2)\n",
        );
        assert!(suggestions.is_empty());
    }
}
