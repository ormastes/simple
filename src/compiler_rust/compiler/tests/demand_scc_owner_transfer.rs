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
    let integration_path = repository.join("src/compiler/80.driver/action_graph/demand_compile_integration.spl");
    let integration = fs::read_to_string(&integration_path).expect("read integration");

    assert!(integration.contains("execution: DemandCompileExecutionV1, cache_root: text,"));
    assert!(!integration.contains("execution: &mut DemandCompileExecutionV1, cache_root: text,"));
    assert!(integration.contains(") -> DemandCompileSccCompletionV1:"));
    assert!(integration.contains("DemandCompileSccCompletionV1(owned, true, \"ok\")"));
    let publish = integration
        .find("val published = scc_compile_outputs_publish_v1(")
        .expect("publication call");
    let link_counter = integration[publish..]
        .find("demand_compile_counter_add_phase_v1(")
        .map(|offset| publish + offset)
        .expect("link counter update");
    assert!(publish < link_counter);

    let native = fs::read_to_string(repository.join("src/compiler/80.driver/driver_aot_native_output.spl"))
        .expect("read native caller");
    let native_success = native
        .rfind("ctx.demand_scc_publication = Some(ownership)")
        .expect("native success restores publication owner");
    let native_execution = native[native_success..]
        .find("ctx.demand_compile_execution = Some(execution)")
        .map(|offset| native_success + offset)
        .expect("native success restores execution owner");
    let native_true = native[native_execution..]
        .find("\n    true")
        .map(|offset| native_execution + offset)
        .expect("native successful return");
    assert!(native_success < native_execution && native_execution < native_true);

    let smf = fs::read_to_string(repository.join("src/compiler/80.driver/driver_aot_smf_output.spl"))
        .expect("read SMF caller");
    let ownership_take = smf
        .find("var ownership = ctx.demand_scc_publication!")
        .expect("SMF publication owner take");
    let execution_take = smf[ownership_take..]
        .find("var execution = ctx.demand_compile_execution!")
        .map(|offset| ownership_take + offset)
        .expect("SMF execution owner take");
    let smf_completion = smf.find("scc_publication_complete_smf_v1(").expect("SMF completion");
    assert!(ownership_take < execution_take && execution_take < smf_completion);
    let early_failure = &smf[smf_completion
        ..smf
            .find("val dirty = ctx.demand_dirty_modules[0]")
            .expect("SMF authority construction")];
    assert!(early_failure.contains("ctx.demand_scc_publication = Some(ownership)"));
    assert!(early_failure.contains("ctx.demand_compile_execution = Some(execution)"));

    for relative in [
        "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
        "src/compiler/80.driver/driver_aot_native_output.spl",
        "src/compiler/80.driver/driver_aot_smf_output.spl",
        "test/03_system/compiler/feature/demand_compile_owner_result_spec.spl",
    ] {
        parse_source(&repository, relative);
    }
}
