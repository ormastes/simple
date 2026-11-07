use super::{
    copy_normalize_path_input, normalize_legacy_path_into, rt_path_normalize,
    NORMALIZE_PATH_CAPACITY,
};
use crate::value::collections::{
    rt_array_free, rt_array_new, rt_string_free, rt_string_new, RuntimeString,
};
use crate::value::heap::{with_typed_ptr, HeapObjectType};
use crate::value::RuntimeValue;

fn text_bytes(value: RuntimeValue) -> Vec<u8> {
    with_typed_ptr::<RuntimeString, _>(value, HeapObjectType::String, |ptr| unsafe {
        (*ptr).as_bytes().to_vec()
    })
    .expect("normalization must return a registered Rust string")
}

fn check_normalized(input: &str, expected: &str) {
    let value = rt_string_new(input.as_ptr(), input.len() as u64);
    let result = rt_path_normalize(value);
    assert_eq!(text_bytes(result), expected.as_bytes(), "input: {input:?}");
    // The result owns its bytes; freeing it must not invalidate the input.
    if result.to_raw() != value.to_raw() {
        rt_string_free(result);
        assert_eq!(text_bytes(value), input.as_bytes());
    }
    rt_string_free(value);
}

#[test]
fn rt_path_normalize_exact_lexical_cases() {
    for (input, expected) in [
        ("", "."),
        (".", "."),
        ("././", "."),
        ("a//b/./c", "a/b/c"),
        (r"a\b\..\c", "a/c"),
        ("a/../b", "b"),
        ("a/b/..", "a"),
        ("../../a", "../../a"),
        ("../a/../../b", "../../b"),
        ("/../../a", "/a"),
        ("/a/../", "/"),
        ("//", "/"),
        ("C:", "C:"),
        ("C:.", "C:"),
        ("C:..", "C:.."),
        ("C:foo/..", "C:"),
        ("C:/a/../../b", "C:/b"),
        (r"\\server\share\..", "/server"),
        (r"\\?\C:\a", "/?/C:/a"),
        ("é/../한글", "한글"),
        ("not-a-real-root/../missing-child", "missing-child"),
        (" spaced / .hidden ", " spaced / .hidden "),
    ] {
        check_normalized(input, expected);
    }
}

#[test]
fn rt_path_normalize_first_nul_after_full_length_check() {
    check_normalized("a\0/ignored", "a");
    check_normalized("\0ignored", ".");

    let accepted = format!("a\0{}", "x".repeat(NORMALIZE_PATH_CAPACITY - 3));
    assert_eq!(accepted.len(), NORMALIZE_PATH_CAPACITY - 1);
    check_normalized(&accepted, "a");

    let rejected = format!("a\0{}", "x".repeat(NORMALIZE_PATH_CAPACITY - 2));
    assert_eq!(rejected.len(), NORMALIZE_PATH_CAPACITY);
    check_normalized(&rejected, "");
}

#[test]
fn rt_path_normalize_byte_length_boundaries() {
    let ascii = "a".repeat(NORMALIZE_PATH_CAPACITY - 1);
    check_normalized(&ascii, &ascii);
    check_normalized(&"a".repeat(NORMALIZE_PATH_CAPACITY), "");

    let unicode = format!("{}a", "é".repeat(2047));
    assert_eq!(unicode.len(), NORMALIZE_PATH_CAPACITY - 1);
    check_normalized(&unicode, &unicode);
    check_normalized(&"é".repeat(2048), "");
}

#[test]
fn rt_path_normalize_rejects_invalid_or_wrong_kind_values() {
    let array = rt_array_new(0);
    for value in [
        RuntimeValue::NIL,
        RuntimeValue::from_int(42),
        RuntimeValue::from_raw(0xdead_0001),
        array,
    ] {
        let result = rt_path_normalize(value);
        assert_eq!(text_bytes(result), b"");
        rt_string_free(result);
    }
    rt_array_free(array);
}

#[test]
fn rt_path_normalize_validates_copied_utf8_before_nul_truncation() {
    // The raw runtime constructor copies bytes without forming an &str.
    // Simulate a malformed foreign value, and never interpret it as text.
    let invalid = [b'a', 0, 0xff];
    let value = rt_string_new(invalid.as_ptr(), invalid.len() as u64);
    let result = rt_path_normalize(value);
    assert_eq!(text_bytes(result), b"");
    rt_string_free(result);
    rt_string_free(value);
}

#[test]
fn rt_path_normalize_snapshot_survives_input_release() {
    let original = b"discarded/../retained";
    let value = rt_string_new(original.as_ptr(), original.len() as u64);
    let mut input = [0u8; NORMALIZE_PATH_CAPACITY];
    let copied = copy_normalize_path_input(value, &mut input).unwrap();
    rt_string_free(value);

    // This is the exact production copy helper. No heap pointer survives it.
    let mut output = [0u8; NORMALIZE_PATH_CAPACITY];
    let length = normalize_legacy_path_into(&input[..copied], &mut output).unwrap();
    assert_eq!(&output[..length], b"retained");
}
