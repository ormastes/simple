use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn execution_metrics_parses_and_lowers_with_project_context() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = repository.join("src/lib/common/perf/execution_metrics.spl");
    let source = fs::read_to_string(&path).expect("read execution metrics source");

    assert!(source.contains("if (baseline_duration_ms <= 0.0 or candidate_duration_ms < 0.0 or"));
    assert!(source.contains(
        "baseline_completed_work <= 0 or minimum_retained_work_percent < 0):"
    ));

    let ast = Parser::new(&source).parse().expect("parse execution metrics");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(&repository))
        .expect("strict project-aware execution metrics lowering");
}
