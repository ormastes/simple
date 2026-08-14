use simple_compiler::interpreter;
use simple_compiler::value::Value;
use std::collections::HashSet;
use std::fs;
use std::sync::Arc;
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

#[test]
fn packed_byte_concat_preserves_storage() {
    let source = r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_array_concat(left: [u8], right: [u8]) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    var left = rt_byte_array_new(0)
    var right = rt_byte_array_new(0)
    left.push(1u8)
    left.push(2u8)
    right.push(3u8)
    right.push(4u8)
    val joined = rt_array_concat(left, right)
    return (joined.len() * 1000 + rt_bytes_u8_at(joined, 0) * 100 + rt_bytes_u8_at(joined, 3)).to_i32()
"#;
    assert_eq!(run_program(source), Ok(4104));
}

#[test]
fn packed_byte_clone_preserves_cow_storage() {
    let original = Value::byte_array(vec![5, 6, 7]);
    let mut cloned = original.clone();
    let (Value::ByteArray(original_bytes), Value::ByteArray(cloned_bytes)) = (&original, &mut cloned) else {
        panic!("packed byte clone changed representation")
    };

    assert!(Arc::ptr_eq(original_bytes, cloned_bytes));
    Arc::make_mut(cloned_bytes)[1] = 9;
    assert_eq!(original.byte_array_view(), Some([5, 6, 7].as_slice()));
    assert_eq!(cloned.byte_array_view(), Some([5, 9, 7].as_slice()));
}

#[test]
fn packed_byte_equality_is_value_based() {
    let packed = Value::byte_array(vec![0, 127, 255]);
    let distinct_packed = Value::byte_array(vec![0, 127, 255]);
    let generic = Value::array(vec![
        Value::Int(0),
        Value::UInt { value: 127, width: 8 },
        Value::Int(255),
    ]);

    assert_eq!(packed, distinct_packed);
    assert_eq!(packed, generic);
    assert_ne!(packed, Value::byte_array(vec![0, 127, 254]));
}
