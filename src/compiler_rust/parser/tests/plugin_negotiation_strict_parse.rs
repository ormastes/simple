use std::fs;
use std::path::PathBuf;

fn negotiation_source() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../lib/common/plugin/negotiation.spl");
    fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
}

#[test]
fn plugin_negotiation_parses_with_strict_match_catch_all() {
    let source = negotiation_source();
    simple_parser::Parser::new(&source)
        .parse()
        .unwrap_or_else(|error| panic!("plugin negotiation must parse: {error:?}"));

    assert!(source.contains("case Ok: true"));
    assert!(source.contains("case OkAbiDeferred: true"));
    assert!(source.contains("case _: false"));
    assert!(!source.contains("\n            else: false"));
}
