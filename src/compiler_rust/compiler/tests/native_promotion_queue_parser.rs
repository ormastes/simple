use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn native_promotion_queue_parses_and_lowers_with_project_context() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = repository.join("src/compiler/80.driver/backend/native_promotion_queue.spl");
    let source = fs::read_to_string(&path).expect("read native promotion queue");

    assert!(source.contains(
        "val completed_ordinal = if result.completed_build_ordinal > entry.request.requested_build_ordinal: result.completed_build_ordinal else: entry.request.requested_build_ordinal"
    ));
    assert!(!source.contains("val completed_ordinal = if result.completed_build_ordinal >\n"));

    let ast = Parser::new(&source)
        .parse()
        .expect("parse native promotion queue");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(&repository))
        .expect("strict project-aware native promotion queue lowering");
}
