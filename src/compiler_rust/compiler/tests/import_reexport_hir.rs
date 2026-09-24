use simple_compiler::hir::{Lowerer, TypeId};
use simple_compiler::module_resolver::ModuleResolver;
use simple_parser::Parser;
use std::fs;
use tempfile::tempdir;

#[test]
fn lowers_field_access_through_reexported_use_shim() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let app_io = src.join("app").join("io");
    let app_cli = src.join("app").join("cli");
    fs::create_dir_all(&app_io).unwrap();
    fs::create_dir_all(&app_cli).unwrap();

    fs::write(
        app_io.join("process_ops.spl"),
        r#"
struct ProcessResult:
    stdout: text
    stderr: text
    exit_code: i64

fn shell(cmd: text) -> ProcessResult:
    ProcessResult(stdout: cmd, stderr: "", exit_code: 0)
"#,
    )
    .unwrap();
    fs::write(
        app_io.join("mod.spl"),
        "use app.io.process_ops.{ProcessResult, shell}\n",
    )
    .unwrap();

    let main_path = app_cli.join("main.spl");
    fs::write(
        &main_path,
        r#"
use app.io.mod (shell)

fn test() -> i64:
    val result = shell("echo hi")
    result.exit_code
"#,
    )
    .unwrap();

    let source = fs::read_to_string(&main_path).unwrap();
    let mut parser = Parser::new(&source);
    let ast = parser.parse().expect("parse failed");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
    let lowered = lowerer.lower_module(&ast).expect("HIR lowering should succeed");

    let test_fn = lowered
        .functions
        .iter()
        .find(|function| function.name == "test")
        .expect("test function should exist");
    assert_eq!(test_fn.return_type, TypeId::I64);
}

#[test]
fn lowers_direct_call_field_access_through_export_use_shim() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let app_io = src.join("app").join("io");
    let app_cli = src.join("app").join("cli");
    fs::create_dir_all(&app_io).unwrap();
    fs::create_dir_all(&app_cli).unwrap();

    fs::write(
        app_io.join("process_ops.spl"),
        r#"
struct ProcessResult:
    stdout: text
    stderr: text
    exit_code: i64

fn shell(cmd: text) -> ProcessResult:
    ProcessResult(stdout: cmd, stderr: "", exit_code: 0)
"#,
    )
    .unwrap();
    fs::write(
        app_io.join("mod.spl"),
        "export use app.io.process_ops.{ProcessResult, shell}\n",
    )
    .unwrap();

    let main_path = app_cli.join("main.spl");
    fs::write(
        &main_path,
        r#"
use app.io.mod (shell)

fn test() -> text:
    shell("echo hi").stdout
"#,
    )
    .unwrap();

    let source = fs::read_to_string(&main_path).unwrap();
    let mut parser = Parser::new(&source);
    let ast = parser.parse().expect("parse failed");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
    let lowered = lowerer.lower_module(&ast).expect("HIR lowering should succeed");

    let test_fn = lowered
        .functions
        .iter()
        .find(|function| function.name == "test")
        .expect("test function should exist");
    assert_eq!(test_fn.return_type, TypeId::STRING);
}

#[test]
fn selective_reexport_alias_preserves_optional_array_return_type() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let leaf = src.join("lib").join("leaf");
    let facade = src.join("lib").join("facade");
    let app = src.join("app");
    fs::create_dir_all(&leaf).unwrap();
    fs::create_dir_all(&facade).unwrap();
    fs::create_dir_all(&app).unwrap();
    fs::write(leaf.join("snapshot.spl"), "extern fn snapshot() -> [(text, text)]?\n").unwrap();
    fs::write(
        facade.join("mod.spl"),
        "export use lib.leaf.snapshot (snapshot as snapshot_nilable)\n",
    )
    .unwrap();
    let main_path = app.join("main.spl");
    fs::write(
        &main_path,
        r#"
use lib.facade.mod (snapshot_nilable as imported_snapshot)

fn count() -> i64:
    val entries = imported_snapshot() ?? []
    var seen = 0
    for pair in entries:
        val (key, value) = pair
        seen = seen + key.len() + value.len()
    entries.len() + seen
"#,
    )
    .unwrap();
    let source = fs::read_to_string(&main_path).unwrap();
    let ast = Parser::new(&source).parse().expect("parse failed");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
    Lowerer::with_module_resolver(resolver, main_path)
        .lower_module(&ast)
        .expect("nested selective aliases must preserve the declared extern return type");
}
