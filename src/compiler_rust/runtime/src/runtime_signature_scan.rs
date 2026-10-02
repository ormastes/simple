//! Dependency-free reader for the compiler-owned runtime ABI table.
//!
//! The runtime build script uses this to retain symbols with the same scalar
//! ABI that Cranelift/LLVM use. It accepts canonical `RuntimeFuncSpec::new`
//! calls across rustfmt line breaks and rejects unknown ABI types.

use std::collections::HashMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RuntimeSignature {
    pub(crate) params: Vec<String>,
    pub(crate) returns: Vec<String>,
}

pub(crate) fn runtime_signatures(source: &str) -> Result<HashMap<String, RuntimeSignature>, String> {
    const MARKER: &str = "RuntimeFuncSpec::new(";
    const MAX_DECLARATION_BYTES: usize = 16_384;
    const MAX_DECLARATION_LINES: usize = 128;
    let mut signatures = HashMap::new();
    let mut lines = source.lines().enumerate();
    while let Some((line_index, line)) = lines.next() {
        let Some((_, mut fragment)) = line.split_once(MARKER) else {
            continue;
        };
        let mut declaration = String::new();
        let mut line_count = 1;
        loop {
            let closing = fragment.find(')');
            if let Some(next) = fragment.find(MARKER) {
                if closing.map_or(true, |end| next < end) {
                    return Err(format!(
                        "line {} has an unterminated runtime declaration before the next spec",
                        line_index + 1
                    ));
                }
            }
            let part = closing.map_or(fragment, |end| &fragment[..=end]);
            if declaration.len() + part.len() > MAX_DECLARATION_BYTES {
                return Err(format!(
                    "line {} runtime declaration exceeds byte bound",
                    line_index + 1
                ));
            }
            declaration.push_str(part);
            if closing.is_some() {
                break;
            }
            if line_count >= MAX_DECLARATION_LINES {
                return Err(format!(
                    "line {} runtime declaration exceeds line bound",
                    line_index + 1
                ));
            }
            let Some((_, next_line)) = lines.next() else {
                return Err(format!(
                    "line {} has an unterminated runtime declaration",
                    line_index + 1
                ));
            };
            declaration.push('\n');
            fragment = next_line;
            line_count += 1;
        }
        let Some(tail) = declaration.trim_start().strip_prefix('"') else {
            return Err(format!("line {} is missing a quoted runtime symbol", line_index + 1));
        };
        let Some((name, tail)) = tail.split_once('"') else {
            return Err(format!("line {} has an unterminated runtime symbol", line_index + 1));
        };
        let (params, tail) = parse_type_list(tail, line_index)?;
        let (returns, tail) = parse_type_list(tail, line_index)?;
        let tail = tail.trim_start();
        let tail = tail.strip_prefix(',').unwrap_or(tail).trim_start();
        if tail != ")" {
            return Err(format!(
                "line {} has an invalid runtime declaration terminator",
                line_index + 1
            ));
        }
        if signatures
            .insert(name.to_string(), RuntimeSignature { params, returns })
            .is_some()
        {
            return Err(format!("duplicate runtime ABI spec for {name}"));
        }
    }
    Ok(signatures)
}

fn parse_type_list(input: &str, line_index: usize) -> Result<(Vec<String>, &str), String> {
    let Some((_, tail)) = input.split_once("&[") else {
        return Err(format!("line {} is missing an ABI type list", line_index + 1));
    };
    let Some((list, tail)) = tail.split_once(']') else {
        return Err(format!("line {} has an unterminated ABI type list", line_index + 1));
    };
    let mut types = Vec::new();
    for item in list.split(',').map(str::trim).filter(|item| !item.is_empty()) {
        match item {
            "I8" | "I32" | "I64" | "F64" => types.push(item.to_string()),
            other => return Err(format!("line {} uses unknown ABI type {other}", line_index + 1)),
        }
    }
    Ok((types, tail))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_canonical_scalar_runtime_specs() {
        let source = r#"
            RuntimeFuncSpec::new("rt_void", &[I64, F64], &[]),
            RuntimeFuncSpec::new("rt_value", &[], &[I32]),
        "#;
        let specs = runtime_signatures(source).unwrap();
        assert_eq!(
            specs["rt_void"],
            RuntimeSignature {
                params: vec!["I64".into(), "F64".into()],
                returns: vec![],
            }
        );
        assert_eq!(specs["rt_value"].returns, ["I32"]);
    }

    #[test]
    fn reads_eighteen_word_linux_start_across_rustfmt_line_breaks() {
        for source in [
            r#"RuntimeFuncSpec::new("rt_linux_group_start_v1",
                &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
                &[I64]),"#,
            r#"RuntimeFuncSpec::new(
                "rt_linux_group_start_v1",
                &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
                &[I64],
            ),"#,
        ] {
            let specs = runtime_signatures(source).unwrap();
            assert_eq!(specs.len(), 1);
            assert_eq!(specs["rt_linux_group_start_v1"].params, vec!["I64"; 18]);
            assert_eq!(specs["rt_linux_group_start_v1"].returns, ["I64"]);
        }
    }

    #[test]
    fn malformed_declaration_cannot_borrow_the_next_specs_type_lists() {
        for broken in [
            "RuntimeFuncSpec::new(\"rt_broken\",",
            "RuntimeFuncSpec::new(\n    \"rt_broken\", &[I64],",
        ] {
            let source = format!("{broken}\nRuntimeFuncSpec::new(\"rt_next\", &[], &[I64]),");
            let error = runtime_signatures(&source).unwrap_err();
            assert!(error.contains("line 1"), "{error}");
            assert!(error.contains("before the next spec"), "{error}");
        }
        assert!(runtime_signatures("RuntimeFuncSpec::new(\"rt_broken\", &[I64],")
            .unwrap_err()
            .contains("unterminated"));
    }

    #[test]
    fn multiline_collection_has_explicit_byte_and_line_bounds() {
        let oversized = format!("RuntimeFuncSpec::new(\"rt_large\", {}", " ".repeat(16_385));
        assert!(runtime_signatures(&oversized).unwrap_err().contains("byte bound"));
        let too_many_lines = format!("RuntimeFuncSpec::new(\"rt_long\",{}", "\n ".repeat(128));
        assert!(runtime_signatures(&too_many_lines).unwrap_err().contains("line bound"));
    }

    #[test]
    fn rejects_duplicate_or_unknown_specs() {
        let duplicate = r#"
            RuntimeFuncSpec::new("rt_same", &[], &[]),
            RuntimeFuncSpec::new("rt_same", &[], &[]),
        "#;
        assert!(runtime_signatures(duplicate).unwrap_err().contains("duplicate"));
        assert!(runtime_signatures(r#"RuntimeFuncSpec::new("rt_bad", &[PTR], &[])"#)
            .unwrap_err()
            .contains("unknown ABI type"));
    }

    #[test]
    fn compiler_registry_supplies_broad_runtime_abi_coverage() {
        let source = include_str!("../../compiler/src/codegen/runtime_sffi.rs");
        let specs = runtime_signatures(source).unwrap();
        assert!(specs.len() >= 1_250, "only {} runtime ABI specs parsed", specs.len());
        assert_eq!(specs["rt_array_push"].params, ["I64", "I64"]);
        assert_eq!(specs["native_tcp_accept"].returns, ["I64", "I64", "I64"]);
        assert_eq!(specs["rt_linux_group_start_v1"].params, vec!["I64"; 18]);
        assert_eq!(specs["rt_linux_group_parent_acquire_v1"].params, ["I64"; 4]);
    }
}
