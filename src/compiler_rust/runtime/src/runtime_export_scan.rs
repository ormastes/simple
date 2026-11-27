//! Small, dependency-free scanner for top-level C function definitions.
//!
//! This is shared by `build.rs` and its unit tests. It intentionally recognizes
//! definitions rather than declarations; the generated provider table takes a
//! real address and must keep the defining archive member reachable.

use std::collections::HashSet;

fn preprocessor_keyword(trimmed: &str) -> Option<&str> {
    let rest = trimmed.strip_prefix('#')?.trim_start();
    let end = rest
        .find(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .unwrap_or(rest.len());
    Some(&rest[..end])
}

fn update_brace_depth(line: &str, depth: &mut usize) {
    let mut chars = line.chars();
    let mut in_string = false;
    let mut in_char = false;
    let mut escaped = false;

    for ch in &mut chars {
        if escaped {
            escaped = false;
            continue;
        }
        if in_string {
            if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }
        if in_char {
            if ch == '\\' {
                escaped = true;
            } else if ch == '\'' {
                in_char = false;
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '\'' => in_char = true,
            '{' => *depth = depth.saturating_add(1),
            '}' => *depth = depth.saturating_sub(1),
            _ => {}
        }
    }
}

pub(crate) fn c_function_definitions(file: &str) -> HashSet<String> {
    let mut exported = HashSet::new();
    let mut declaration = String::new();
    let mut depth = 0usize;
    let mut pp_entry_depths: Vec<usize> = Vec::new();
    let mut in_block_comment = false;
    let mut in_pp_continuation = false;

    for raw_line in file.lines() {
        let line_continues = raw_line.trim_end_matches([' ', '\t', '\r']).ends_with('\\');
        let line = strip_comments(raw_line, &mut in_block_comment);
        let trimmed = line.trim();

        if in_pp_continuation {
            declaration.clear();
            in_pp_continuation = line_continues;
            continue;
        }

        if let Some(kw) = preprocessor_keyword(trimmed) {
            match kw {
                "if" | "ifdef" | "ifndef" => pp_entry_depths.push(depth),
                "elif" | "else" => {
                    if let Some(&entry_depth) = pp_entry_depths.last() {
                        depth = entry_depth;
                    }
                }
                "endif" => {
                    pp_entry_depths.pop();
                }
                _ => {}
            }
            declaration.clear();
            in_pp_continuation = line_continues;
            continue;
        }

        if depth == 0 && !trimmed.is_empty() {
            if !declaration.is_empty() {
                declaration.push(' ');
            }
            declaration.push_str(trimmed);

            if let Some(open) = declaration.find('{') {
                if let Some(symbol) = definition_name(&declaration[..open]) {
                    exported.insert(symbol.to_string());
                }
                declaration.clear();
            } else if declaration.contains(';') {
                declaration.clear();
            }
        }

        update_brace_depth(&line, &mut depth);
    }

    exported
}

fn definition_name(declaration: &str) -> Option<&str> {
    let declaration = declaration.trim();
    if declaration.starts_with("static ") || declaration.starts_with("typedef ") {
        return None;
    }
    let paren = declaration.find('(')?;
    let head = declaration[..paren].trim_end();
    let symbol = head.split_whitespace().last()?.trim_start_matches('*');
    if symbol.is_empty() || !symbol.chars().all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return None;
    }
    Some(symbol)
}

fn strip_comments(line: &str, in_block_comment: &mut bool) -> String {
    let bytes = line.as_bytes();
    let mut clean = String::with_capacity(line.len());
    let mut index = 0usize;
    while index < bytes.len() {
        if *in_block_comment {
            if index + 1 < bytes.len() && bytes[index] == b'*' && bytes[index + 1] == b'/' {
                *in_block_comment = false;
                index += 2;
            } else {
                index += 1;
            }
        } else if index + 1 < bytes.len() && bytes[index] == b'/' && bytes[index + 1] == b'*' {
            *in_block_comment = true;
            index += 2;
        } else if index + 1 < bytes.len() && bytes[index] == b'/' && bytes[index + 1] == b'/' {
            break;
        } else {
            clean.push(bytes[index] as char);
            index += 1;
        }
    }
    clean
}

#[cfg(test)]
mod tests {
    use super::c_function_definitions;

    #[test]
    fn recognizes_single_and_multiline_definitions_but_not_declarations_or_static_helpers() {
        let source = r#"
            uint8_t* rt_struct_alloc(int64_t size) {
                return 0;
            }

            int8_t rt_struct_receiver_valid(
                    int64_t receiver, int64_t byte_offset, int64_t access_width)
            {
                return receiver != 0;
            }

            int8_t declaration_only(int64_t value);
            static int hidden_helper(int value) { return value; }
        "#;
        let names = c_function_definitions(source);
        assert_eq!(names.len(), 2);
        assert!(names.contains("rt_struct_alloc"));
        assert!(names.contains("rt_struct_receiver_valid"));
    }

    #[test]
    fn restores_brace_depth_across_if_else_branches_and_ignores_literals_and_macros() {
        let source = r#"
            #define OPEN_BLOCK do { \
                int ignored = 1;

            int64_t rt_first_fn(int64_t flag) {
                const char* brace = "{";
                char c = '{';
            #ifdef FOO
                if (flag) {
            #else
                if (!flag) {
            #endif
                    return (int64_t)brace[0] + (int64_t)c;
                }
                return 0;
            }

            int64_t rt_after_ifdef_fn(void) { return 42; }
        "#;
        let names = c_function_definitions(source);
        assert!(names.contains("rt_first_fn"));
        assert!(names.contains("rt_after_ifdef_fn"));
        assert_eq!(names.len(), 2);
    }

    #[test]
    fn finds_tail_process_observation_v4_definitions_in_runtime_process_owned() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../runtime/runtime_process_owned.c");
        let source = std::fs::read_to_string(&path).expect("read runtime_process_owned.c");
        let names = c_function_definitions(&source);
        assert!(
            names.contains("rt_process_observation_v4_close_cwd_value"),
            "missing rt_process_observation_v4_close_cwd_value after #ifdef/#else block"
        );
        assert!(
            names.contains("rt_process_observation_v4_reserve_value"),
            "missing rt_process_observation_v4_reserve_value after #ifdef/#else block"
        );
    }
}
