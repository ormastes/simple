//! Bootstrap seed regression: force-unwrapped Some/Ok is a writable place.
use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

#[test]
fn explicit_option_and_result_payload_field_writes_keep_the_original_place() {
    let dir = tempdir().unwrap();
    let source = dir.path().join("main.spl");
    fs::write(&source, include_str!("../../../../test/fixtures/compiler/forceunwrap_place/main.spl")).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(
        &source, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(source));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    assert_eq!(result.map_err(|error| format!("{error:?}")), Ok(0));
}
