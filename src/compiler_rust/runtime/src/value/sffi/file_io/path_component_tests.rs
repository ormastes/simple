use super::{copy_path_component, rt_path_extension, rt_path_filename};
use crate::value::collections::{
    rt_array_free, rt_array_new, rt_string_free, rt_string_new, RuntimeString,
};
use crate::value::heap::{with_typed_ptr, HeapObjectType};
use crate::value::RuntimeValue;

fn bytes(value: RuntimeValue) -> Vec<u8> {
    with_typed_ptr::<RuntimeString, _>(value, HeapObjectType::String, |ptr| unsafe {
        (*ptr).as_bytes().to_vec()
    })
    .expect("component result must be a registered Rust string")
}

fn check(input: &[u8], expected: &[u8], operation: extern "C" fn(RuntimeValue) -> RuntimeValue) {
    let value = rt_string_new(input.as_ptr(), input.len() as u64);
    let result = operation(value);
    assert_eq!(bytes(result), expected, "input: {input:?}");
    // Short-string caches may return the same managed object.
    if result.to_raw() != value.to_raw() {
        rt_string_free(result);
        assert_eq!(bytes(value), input);
    }
    rt_string_free(value);
}

#[test]
fn rt_path_components_filename_lexical_cases() {
    for (input, expected) in [
        ("", ""), ("/", ""), ("///", ""), ("a", "a"),
        ("a/b///", "b"), ("/a//b", "b"), (".", "."), ("..", ".."),
        ("dir/.hidden", ".hidden"), ("C:", "C:"),
        (r"C:\dir\file.ext", r"C:\dir\file.ext"),
        (r"dir/back\slash.ext", r"back\slash.ext"),
        ("한글/é.txt/", "é.txt"),
    ] {
        check(input.as_bytes(), expected.as_bytes(), rt_path_filename);
    }
}

#[test]
fn rt_path_components_extension_lexical_cases() {
    for (input, expected) in [
        ("", ""), ("///", ""), ("a", ""), ("file.", ""),
        (".hidden", ""), ("dir/.hidden", ""), (".hidden.ext", "ext"),
        (".", ""), ("..", ""), ("...x", "x"), ("a.b.c///", "c"),
        ("dir.ext/plain", ""), (r"dir.ext\plain", r"ext\plain"),
        ("한글/파일.확장/", "확장"),
    ] {
        check(input.as_bytes(), expected.as_bytes(), rt_path_extension);
    }
}

#[test]
fn rt_path_components_counted_nul_and_long_paths() {
    check(b"dir/a\0b.ext\0tail///", b"a\0b.ext\0tail", rt_path_filename);
    check(b"dir/a\0b.ext\0tail///", b"ext\0tail", rt_path_extension);
    check(b"prefix\0/last.part", b"last.part", rt_path_filename);
    let filename = format!("{}.{}", "é".repeat(3000), "한".repeat(2000));
    let input = format!("dir/{filename}///");
    assert!(filename.len() > 4096);
    check(input.as_bytes(), filename.as_bytes(), rt_path_filename);
    check(input.as_bytes(), "한".repeat(2000).as_bytes(), rt_path_extension);
}

#[test]
fn rt_path_components_invalid_values_and_utf8() {
    let array = rt_array_new(0);
    for value in [RuntimeValue::NIL, RuntimeValue::from_int(4),
                  RuntimeValue::from_raw(0xdead_0001), array] {
        for operation in [rt_path_filename, rt_path_extension] {
            let result = operation(value);
            assert_eq!(bytes(result), b"");
            rt_string_free(result);
        }
    }
    rt_array_free(array);
    // Malformed bytes outside the selected suffix still invalidate text.
    for input in [&b"bad\xff/valid.ext"[..], &b"valid.ext\0\xff"[..]] {
        check(input, b"", rt_path_filename);
        check(input, b"", rt_path_extension);
    }
}

#[test]
fn rt_path_components_snapshot_survives_input_release() {
    let input = "discard/retained.확장";
    let value = rt_string_new(input.as_ptr(), input.len() as u64);
    let filename = copy_path_component(value, false).unwrap();
    let extension = copy_path_component(value, true).unwrap();
    rt_string_free(value);
    assert_eq!(filename, "retained.확장".as_bytes());
    assert_eq!(extension, "확장".as_bytes());
}

#[test]
fn rt_path_components_result_survives_input_release() {
    for operation in [rt_path_filename, rt_path_extension] {
        let input = "noncached-parent/owned-noncached-filename.owned-extension";
        let value = rt_string_new(input.as_ptr(), input.len() as u64);
        let result = operation(value);
        let expected = bytes(result);
        if result.to_raw() != value.to_raw() {
            rt_string_free(value);
            assert_eq!(bytes(result), expected);
            rt_string_free(result);
        } else {
            rt_string_free(value);
        }
    }
}
