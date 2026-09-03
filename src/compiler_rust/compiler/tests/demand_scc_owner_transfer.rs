use simple_parser::Parser;
use std::fs;
use std::path::{Path, PathBuf};

fn parse_source(repository: &Path, relative: &str) {
    let path = repository.join(relative);
    let source = fs::read_to_string(&path).expect("read source");
    Parser::new(&source).parse().expect("parse source");
}

#[test]
fn demand_scc_publication_consumes_and_returns_execution_owner() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let integration_path = repository
        .join("src/compiler/80.driver/action_graph/demand_compile_integration.spl");
    let integration = fs::read_to_string(&integration_path).expect("read integration");

    assert!(integration.contains(
        "execution: DemandCompileExecutionV1, cache_root: text,"
    ));
    assert!(!integration.contains(
        "execution: &mut DemandCompileExecutionV1, cache_root: text,"
    ));
    assert!(integration.contains(
        ") -> DemandCompileSccCompletionV1:"
    ));
    assert!(integration.contains(
        "DemandCompileSccCompletionV1(owned, true, \"ok\")"
    ));

    for relative in [
        "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
        "src/compiler/80.driver/driver_aot_native_output.spl",
        "src/compiler/80.driver/driver_aot_smf_output.spl",
    ] {
        parse_source(&repository, relative);
    }
}
