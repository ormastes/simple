//! Interpreter regressions found restoring the signed-admission argv/envp spec
//! on an aarch64 host: `u64` division/modulo went through signed `i64`
//! (`u64::MAX / 2 == 0`), and the `@cfg(arm64)` loader byte externs were not
//! registered (`unknown extern function: rt_arm_array_get_byte_u32`).

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
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .map_err(|error| format!("{error:?}"))?;
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items).map_err(|error| format!("{error:?}"));
    interpreter::set_current_file(None);
    result
}

#[test]
fn u64_division_and_modulo_stay_unsigned() {
    let source = r#"
val MAX: u64 = 0xffffffffffffffffu64

fn main() -> i32:
    if MAX / 2 != 0x7fffffffffffffffu64:
        return 1
    if 1u64 > MAX / 2:
        return 2
    if MAX % 10u64 != 5u64:
        return 3
    val small: u32 = 7u32
    if small / 2u32 != 3u32 or small % 4u32 != 3u32:
        return 4
    if -7 / 2 != -3 or -7 % 2 != -1:
        return 5
    return 0
"#;
    assert_eq!(run_program(source), Ok(0));
}

#[test]
fn local_runtime_byte_buffer_accepts_index_assignment() {
    let source = r#"
extern fn rt_byte_array_new_len(len: i64) -> [u8]

fn main() -> i32:
    val bytes = rt_byte_array_new_len(4)
    bytes[1] = 0xABu8
    bytes[3] = 7u8
    if bytes.len() != 4 or bytes[1] != 0xABu8 or bytes[3] != 7u8 or bytes[0] != 0u8:
        return 1
    return 0
"#;
    assert_eq!(run_program(source), Ok(0));
}

#[test]
fn arm_loader_byte_externs_are_registered() {
    let source = r#"
extern fn rt_arm_array_len_u32(arr: [u8]) -> u32
extern fn rt_arm_array_get_byte_u32(arr: [u8], idx: u64) -> u32
extern fn rt_arm_elf64_pt_load_count(bytes: [u8]) -> u32

fn main() -> i32:
    val bytes: [u8] = [1, 2, 250]
    if rt_arm_array_len_u32(bytes) != 3u32:
        return 1
    if rt_arm_array_get_byte_u32(bytes, 2u64) != 250u32:
        return 2
    if rt_arm_array_get_byte_u32(bytes, 3u64) != 0u32:
        return 3
    if rt_arm_elf64_pt_load_count(bytes) != 0u32:
        return 4
    return 0
"#;
    assert_eq!(run_program(source), Ok(0));
}
