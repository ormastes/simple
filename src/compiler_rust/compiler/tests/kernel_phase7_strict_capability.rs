use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

const FILES: [&str; 8] = [
    "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
    "src/compiler/80.driver/demand_mir_evidence_builder.spl",
    "src/compiler/80.driver/smf/runtime_std_package_set.spl",
    "src/compiler/80.driver/action_graph/artifact_service_bridge.spl",
    "src/compiler/80.driver/driver_aot_native_output.spl",
    "src/compiler/80.driver/driver_aot_smf_output.spl",
    "src/compiler/80.driver/driver_pipeline_lowering.spl",
    "src/compiler/80.driver/driver_source_pipeline_loading.spl",
];

#[test]
fn phase7_units_pass_strict_capability_lowering() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let mut failures = Vec::new();

    for relative in FILES {
        let path = repository.join(relative);
        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("STRICT_CAPABILITY_FILE_STATUS path={relative} status=2 error={error}");
                failures.push(relative);
                continue;
            }
        };
        let ast = match Parser::new(&source).parse() {
            Ok(ast) => ast,
            Err(error) => {
                eprintln!("STRICT_CAPABILITY_FILE_STATUS path={relative} status=3 error={error:?}");
                failures.push(relative);
                continue;
            }
        };
        match hir::lower_with_context_and_project_hint(&ast, &path, Some(&repository)) {
            Ok(_) => eprintln!("STRICT_CAPABILITY_FILE_STATUS path={relative} status=0"),
            Err(error) => {
                eprintln!("STRICT_CAPABILITY_FILE_STATUS path={relative} status=4 error={error:?}");
                failures.push(relative);
            }
        }
    }

    assert!(failures.is_empty(), "strict capability failures: {failures:?}");
}
