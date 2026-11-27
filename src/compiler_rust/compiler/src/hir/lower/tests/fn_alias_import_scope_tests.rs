//! Native (non-flattened) lane: a function the entry file explicitly `use`s
//! keeps its own return type when a transitively imported module privately
//! aliases a different function to the same name. Regression for
//! doc/08_tracking/bug/native_text_to_bytes_for_loop_reads_packed_words_when_agent_workspace_linked_2026-11-14.md
use crate::hir::lower::lowerer::Lowerer;
use crate::mir::MirInst;
use crate::module_resolver::ModuleResolver;
use crate::test_helpers::create_test_project;
use simple_parser::Parser;
use std::fs;

const A_BYTES: &str = "fn to_bytes(s: text) -> [u8]:\n    var out: [u8] = []\n    out\n";
const B_WORDS: &str = "fn to_words(s: text) -> [i64]:\n    var out: [i64] = []\n    out\n";
const B_USER: &str = "use b_words.{to_words as to_bytes}\n\nfn b_helper() -> i64:\n    to_bytes(\"x\").len()\n";

/// Runtime element readers `probe`'s for-loop calls, in MIR order.
fn probe_element_readers(entry: &str) -> Vec<String> {
    let dir = create_test_project();
    let src = dir.path().join("src");
    for (name, text) in [("a_bytes.spl", A_BYTES), ("b_words.spl", B_WORDS), ("b_user.spl", B_USER)] {
        fs::write(src.join(name), text).unwrap();
    }
    let ast = Parser::new(entry).parse().expect("parse entry");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let hir = Lowerer::with_module_resolver(resolver, src.join("main.spl"))
        .lower_module(&ast)
        .expect("entry lowers to HIR");
    let mir = crate::mir::lower_to_mir(&hir).expect("entry lowers to MIR");
    let probe = mir.functions.iter().find(|f| f.name == "probe").expect("probe MIR function");
    probe
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|inst| match inst {
            MirInst::Call { target, .. } => Some(target.name().to_string()),
            _ => None,
        })
        .filter(|name| name.starts_with("rt_typed_") || name == "rt_array_get")
        .collect()
}

const PROBE: &str = "fn probe() -> i64:\n    var total = 0\n    for b in to_bytes(\"a-1\"):\n        total = total + b.to_i64()\n    total\n";

#[test]
fn explicit_import_keeps_u8_elements_when_later_dependency_aliases_the_name() {
    let entry = format!("use a_bytes.{{to_bytes}}\nuse b_user.{{b_helper}}\n\n{PROBE}");
    assert_eq!(probe_element_readers(&entry), vec!["rt_typed_bytes_u8_at".to_string()]);
}

#[test]
fn explicit_import_keeps_u8_elements_when_earlier_dependency_aliases_the_name() {
    let entry = format!("use b_user.{{b_helper}}\nuse a_bytes.{{to_bytes}}\n\n{PROBE}");
    assert_eq!(probe_element_readers(&entry), vec!["rt_typed_bytes_u8_at".to_string()]);
}
