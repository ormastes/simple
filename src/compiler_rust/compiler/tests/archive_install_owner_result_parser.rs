use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn archive_install_owner_result_parses_and_lowers_with_project_types() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    for relative in [
        "src/compiler/20.hir/archive/interface_action_archive.spl",
        "src/compiler/80.driver/action_graph/artifact_service_bridge.spl",
        "src/compiler/80.driver/driver_source_pipeline_loading.spl",
        "test/03_system/compiler/feature/archive_install_owner_result_spec.spl",
    ] {
        let path = repository.join(relative);
        let source = fs::read_to_string(&path).expect("read owner-result source");
        let ast = Parser::new(&source).parse().expect("parse owner-result source");
        hir::lower_with_context_and_project_hint(&ast, &path, Some(&repository))
            .expect("lower owner-result source with imported types");
    }
}
