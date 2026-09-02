use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

const FILES: [&str; 6] = [
    "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
    "src/compiler/80.driver/action_graph/artifact_service_bridge.spl",
    "src/compiler/80.driver/driver_aot_native_output.spl",
    "src/compiler/80.driver/driver_aot_smf_output.spl",
    "src/compiler/80.driver/driver_pipeline_lowering.spl",
    "src/compiler/80.driver/driver_source_pipeline_loading.spl",
];

fn lower_source(source: &str) -> Result<(), String> {
    let ast = Parser::new(source).parse().map_err(|error| format!("parse: {error:?}"))?;
    hir::lower(&ast).map(|_| ()).map_err(|error| format!("hir: {error:?}"))
}

#[test]
fn call_scoped_exclusive_loans_end_at_the_call_boundary() {
    let sequential = "fn mutate(value: &mut i64):\n    value = value + 1\n\nfn probe():\n    var value = 0\n    mutate(&mut value)\n    mutate(&mut value)\n";
    assert!(lower_source(sequential).is_ok(), "sequential call-scoped loans must not alias");

    let overlapping = "fn pair(left: &mut i64, right: &mut i64):\n    pass\n\nfn probe():\n    var value = 0\n    pair(&mut value, &mut value)\n";
    let error = lower_source(overlapping).expect_err("same-call exclusive aliases must fail closed");
    assert!(error.contains("AliasingViolation"), "same-call failure must reach capability checking: {error}");
}

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
