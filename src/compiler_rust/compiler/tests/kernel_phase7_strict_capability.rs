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
    let sequential = "fn inspect(value: &mut i64) -> i64:\n    pass\n\nfn probe():\n    var value = 0\n    inspect(&mut value)\n    inspect(&mut value)\n";
    assert!(lower_source(sequential).is_ok(), "sequential call-scoped loans must not alias");

    let overlapping = "fn pair(left: &mut i64, right: &mut i64):\n    pass\n\nfn probe():\n    var value = 0\n    pair(&mut value, &mut value)\n";
    let error = lower_source(overlapping).expect_err("same-call exclusive aliases must fail closed");
    assert!(error.contains("AliasingViolation"), "same-call failure must reach capability checking: {error}");

    let returned = "fn retain(value: &mut i64) -> &mut i64:\n    value\n\nfn probe():\n    var value = 0\n    val retained = retain(&mut value)\n    retain(&mut value)\n";
    assert!(lower_source(returned).expect_err("returned exclusive loan must survive the call").contains("AliasingViolation"));

    let stored = "fn store(value: &mut i64):\n    val capture = fn(): value\n\nfn probe():\n    var value = 0\n    store(&mut value)\n    store(&mut value)\n";
    assert!(lower_source(stored).expect_err("unrestricted store/capture call must conservatively retain its loan").contains("AliasingViolation"));

    let forged_pure = "@pure\nfn store(value: &mut i64):\n    val capture = fn(): value\n\nfn probe():\n    var value = 0\n    store(&mut value)\n    store(&mut value)\n";
    assert!(lower_source(forged_pure).expect_err("@pure must not forge noescape authority").contains("AliasingViolation"));

    let unresolved_pure = "@pure\nfn probe(store: any):\n    var value = 0\n    store(&mut value)\n    store(&mut value)\n";
    assert!(lower_source(unresolved_pure).expect_err("unresolved pure signatures remain escaping").contains("AliasingViolation"));

    let nested_error = "fn inspect(value: &mut i64) -> i64:\n    pass\n\nfn probe():\n    var value = 0\n    inspect(&mut value)\n    unknown(&mut value)\n    inspect(&mut value)\n";
    assert!(lower_source(nested_error).is_err(), "error paths must fail closed without discarding persistent loans");
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
