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
    Regex::new(&format!(r#"^\s*{}\.(?P<method>[A-Za-z_][A-Za-z0-9_]*)\(\)\s*$"#, regex::escape(param)))
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
        && !trimmed.contains("=")
}

fn replacement_for(param: &str, body: &str) -> Option<String> {
    let body = body.trim();
    if !is_readable_short_candidate(body) {
        return None;
    }

    let ident = plain_identifier_regex(param);
    if !ident.is_match(body) {
        return Some(format!("\\_: {}", body));
    }

    if let Some(captures) = method_ref_regex(param).captures(body) {
        if let Some(method) = captures.name("method") {
            return Some(format!("&:{}", method.as_str()));
        }
    }

    let replaced = ident.replace_all(body, "_1").to_string();
    if replaced == body {
        None
    } else {
        Some(replaced)
    }
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
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val separators = headers.map(\\h: \"---\")\n");
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].replacement, "\\_: \"---\"");
    }

    #[test]
    fn ignores_existing_wildcard_callbacks() {
        let suggestions = collect_short_grammar_suggestions("fn f():\n    val separators = headers.map(\\_: \"---\")\n");
        assert!(suggestions.is_empty());
    }
}
