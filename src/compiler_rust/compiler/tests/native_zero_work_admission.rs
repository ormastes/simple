use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

fn parse_and_lower(repository: &PathBuf, relative: &str) {
    let path = repository.join(relative);
    let source = fs::read_to_string(&path).expect("read source");
    let ast = Parser::new(&source).parse().expect("parse source");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(repository))
        .expect("project-aware lowering");
}

#[test]
fn native_zero_work_admission_precedes_every_compiler_phase() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let orchestration_path = repository.join("src/compiler/80.driver/driver_orchestration.spl");
    let orchestration = fs::read_to_string(orchestration_path).expect("read orchestration");
    let admission = orchestration.find("native_noop_admit_v1(native_noop_request)")
        .expect("preflight admission");
    for phase in [
        "log_phase(\"compile:start\")",
        "self.load_sources_impl()",
        "self.parse_all_committing_impl()",
        "self.lower_to_mir()",
    ] {
        let scheduled = orchestration.find(phase).expect("scheduled phase");
        assert!(admission < scheduled, "admission must precede {phase}");
    }
    assert!(orchestration.contains("compiler_work_counters_zero_v1(work)"));
    assert!(orchestration.contains("compiler_work_parser_schedule_v1"));
    assert!(orchestration.contains("compiler_work_hir_schedule_v1"));
    let aot = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_aot_pipeline.spl")).expect("read aot pipeline");
    let native = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_aot_native_output.spl")).expect("read native output");
    assert!(aot.contains("compiler_work_mir_schedule_v1"));
    assert!(native.contains("compiler_work_codegen_schedule_v1"));
    assert!(native.contains("compiler_work_link_schedule_v1"));
    let protocol = fs::read_to_string(repository.join(
        "src/compiler/80.driver/cache/native_noop_admission.spl")).expect("read protocol");
    assert!(protocol.contains("content-digest="));
    assert!(protocol.contains("file_create_excl(staged, encoded)"));
    for point in ["generation-write", "generation-rename", "pointer-write", "pointer-rename"] {
        assert!(protocol.contains(point));
    }
    parse_and_lower(&repository, "src/compiler/80.driver/cache/native_noop_admission.spl");
    parse_and_lower(&repository, "src/compiler/80.driver/perf/compiler_work_counters.spl");
    parse_and_lower(&repository, "src/compiler/80.driver/driver_orchestration.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/native_zero_work_admission_spec.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/native_zero_work_crash_probe.spl");
}
