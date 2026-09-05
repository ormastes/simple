//! Small, dependency-free scanner for top-level C function definitions.
//!
//! This is shared by `build.rs` and its unit tests. It intentionally recognizes
//! definitions rather than declarations; the generated provider table takes a
//! real address and must keep the defining archive member reachable.

use std::collections::HashSet;

pub(crate) fn c_function_definitions(file: &str) -> HashSet<String> {
    let mut exported = HashSet::new();
    let mut declaration = String::new();
    let mut depth = 0usize;
    let mut in_block_comment = false;

    for raw_line in file.lines() {
        let line = strip_comments(raw_line, &mut in_block_comment);

        if depth == 0 {
            let trimmed = line.trim();
            if trimmed.starts_with('#') {
                declaration.clear();
            } else if !trimmed.is_empty() {
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
        }

        for ch in line.chars() {
            match ch {
                '{' => depth = depth.saturating_add(1),
                '}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
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
}
