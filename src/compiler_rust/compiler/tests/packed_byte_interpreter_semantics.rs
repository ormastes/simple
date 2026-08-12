use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_program(source: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, source).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(
        &main_path,
        &mut HashSet::new(),
    )
    .map_err(|error| format!("{error:?}"))?;
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items).map_err(|error| format!("{error:?}"));
    interpreter::set_current_file(None);
    result
}

#[test]
fn packed_bytes_cover_index_slice_iteration_widening_and_freeze() {
    let success = r#"
extern fn rt_bytes_alloc(len: u64) -> [u8]

fn main() -> i32:
    var bytes = rt_bytes_alloc(4u64)
    if bytes[0] != 0u8:
        return 1
    val middle = bytes[1:3]
    if middle.len() != 2:
        return 2
    var count = 0
    for byte in bytes:
        count = count + byte.to_i64()
    if count != 0:
        return 3
    bytes.push(7u8)
    if bytes.len() != 5 or bytes[4] != 7u8:
        return 4
    bytes.push(300)
    if bytes.len() != 6 or bytes[5] != 300:
        return 5
    return 0
"#;
    assert_eq!(run_program(success), Ok(0));

    let frozen_mutation = r#"
extern fn rt_bytes_alloc(len: u64) -> [u8]

fn main() -> i32:
    val frozen = freeze(rt_bytes_alloc(2u64))
    frozen.push(1u8)
    return 0
"#;
    let error = run_program(frozen_mutation).expect_err("frozen packed bytes must reject mutation");
    assert!(error.contains("frozen byte array"), "unexpected error: {error}");
}
