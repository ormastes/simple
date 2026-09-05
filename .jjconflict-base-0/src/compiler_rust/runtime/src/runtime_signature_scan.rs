//! Dependency-free reader for the compiler-owned runtime ABI table.
//!
//! The runtime build script uses this to retain symbols with the same scalar
//! ABI that Cranelift/LLVM use. It deliberately accepts only the compact,
//! canonical `RuntimeFuncSpec::new` form and rejects unknown ABI types.

use std::collections::HashMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RuntimeSignature {
    pub(crate) params: Vec<String>,
    pub(crate) returns: Vec<String>,
}

pub(crate) fn runtime_signatures(source: &str) -> Result<HashMap<String, RuntimeSignature>, String> {
    let mut signatures = HashMap::new();
    for (line_index, line) in source.lines().enumerate() {
        let Some((_, tail)) = line.split_once("RuntimeFuncSpec::new(\"") else {
            continue;
        };
        let Some((name, tail)) = tail.split_once('"') else {
            return Err(format!("line {} has an unterminated runtime symbol", line_index + 1));
        };
        let (params, tail) = parse_type_list(tail, line_index)?;
        let (returns, _) = parse_type_list(tail, line_index)?;
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
    }
}
