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
    assert!(orchestration.contains(
        "parser=0 hir=0 mir=0 codegen=0 link=0"
    ));
    parse_and_lower(&repository, "src/compiler/80.driver/cache/native_noop_admission.spl");
    parse_and_lower(&repository, "src/compiler/80.driver/driver_orchestration.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/native_zero_work_admission_spec.spl");
}
