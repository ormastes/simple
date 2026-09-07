use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn demand_counter_owner_transfer_parses_and_lowers_without_exclusive_aliasing() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    for relative in [
        "src/compiler/80.driver/perf/demand_compile_counters.spl",
        "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
        "test/03_system/compiler/feature/demand_compile_owner_result_spec.spl",
    ] {
        let path = repository.join(relative);
        let source = fs::read_to_string(&path).expect("read counter owner-result source");
        Parser::new(&source).parse().expect("parse counter owner-result source");
    }

    let owner_transfer = r#"
struct Counters:
    total: i64

struct Transfer:
    counters: Counters
    accepted: bool

fn update(counters: Counters, accepted: bool) -> Transfer:
    Transfer(Counters(counters.total + 1), accepted)

fn finalize(counters: Counters) -> Counters:
    var counters = counters
    val baseline_counter = update(counters, true)
    counters = baseline_counter.counters
    val total_counter = update(counters, true)
    counters = total_counter.counters
    counters
"#;
    let owner_ast = Parser::new(owner_transfer).parse().expect("parse owned counter chain");
    hir::lower(&owner_ast).expect("lower owned counter chain without exclusive aliasing");

    let integration = fs::read_to_string(repository.join(
        "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
    ))
    .expect("read demand compile integration");
    assert!(!integration.contains(
        "&mut counters, \"baseline-backend\", baseline_started_ns",
    ));
    assert!(!integration.contains("&mut counters, \"total\", total_started_ns"));
    assert_eq!(
        integration
            .matches("demand_compile_counter_add_phase_owned_v1(")
            .count(),
        2,
    );
}
