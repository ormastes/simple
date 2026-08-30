//! An explicit import binding is authoritative even when an unimported,
//! same-named overload would accept the supplied arguments.

use simple_compiler::interpreter;
use simple_compiler::pipeline::module_loader::load_module_with_imports;
use std::collections::HashSet;
use std::fs;

#[test]
fn incompatible_imported_overload_does_not_escape_to_unimported_module() {
    let dir = tempfile::tempdir().expect("create fixture directory");
    fs::write(dir.path().join("mod_a.spl"), "fn choose(value: i64) -> i32:\n    11\n")
        .expect("write imported authority module");
    fs::write(
        dir.path().join("mod_b.spl"),
        "fn choose(value: text) -> i32:\n    22\n\nfn anchor() -> i32:\n    0\n",
    )
    .expect("write co-compiled unimported-overload module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use mod_a.{choose}\nuse mod_b.{anchor}\n\nfn main() -> i32:\n    choose(\"text\")\n",
    )
    .expect("write entry module");

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = load_module_with_imports(&main_path, &mut HashSet::new()).expect("flatten fixture modules");
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);

    let error = result.expect_err("the unimported text overload must not satisfy mod_a's binding");
    assert!(
        error
            .to_string()
            .contains("no caller-authorized overload of `choose` matches"),
        "unexpected authority failure: {error}"
    );
}
