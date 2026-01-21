//! Tests for deprecation warnings (generic syntax migration from [] to <>)

use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::Parser;

/// Helper to parse and check for warnings
fn parse_and_get_hints(src: &str) -> Vec<(ErrorHintLevel, String)> {
    let mut parser = Parser::new(src);
    let _ = parser.parse(); // Parse (may succeed or fail, we just want hints)

    parser
        .error_hints()
        .iter()
        .map(|h| (h.level, h.message.clone()))
        .collect()
}

/// Helper to check if there's a deprecation warning
fn has_deprecation_warning(src: &str) -> bool {
    let hints = parse_and_get_hints(src);
    hints.iter().any(|(level, msg)| {
        matches!(level, ErrorHintLevel::Warning)
            && (msg.contains("Deprecated syntax for generic") || msg.contains("Deprecated syntax for type"))
    })
}

/// Helper to count deprecation warnings
fn count_deprecation_warnings(src: &str) -> usize {
    let hints = parse_and_get_hints(src);
    hints
        .iter()
        .filter(|(level, msg)| {
            matches!(level, ErrorHintLevel::Warning)
                && (msg.contains("Deprecated syntax for generic") || msg.contains("Deprecated syntax for type"))
        })
        .count()
}

// === Function Generic Parameters ===

#[test]
fn test_deprecated_function_generic_params() {
    let src = "fn test[T](x: T) -> T:\n    x";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in function generics"
    );
}

#[test]
fn test_deprecated_function_multiple_params() {
    let src = "fn map[T, U](f: fn(T) -> U) -> U:\n    pass";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax with multiple params"
    );
}

#[test]
fn test_new_function_generic_params_no_warning() {
    let src = "fn test<T>(x: T) -> T:\n    x";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in function generics"
    );
}

// === Struct Generic Parameters ===

#[test]
fn test_deprecated_struct_generic() {
    let src = "struct Container[T]:\n    value: T";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in struct"
    );
}

#[test]
fn test_new_struct_generic_no_warning() {
    let src = "struct Container<T>:\n    value: T";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in struct"
    );
}

// === Type Annotations ===

#[test]
fn test_deprecated_type_annotation_option() {
    let src = "val x: Option[Int] = None";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in Option type"
    );
}

#[test]
fn test_deprecated_type_annotation_result() {
    let src = "val x: Result[Int, String] = Ok(42)";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in Result type"
    );
}

#[test]
fn test_deprecated_type_annotation_list() {
    let src = "val nums: List[Int] = []";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in List type"
    );
}

#[test]
fn test_new_type_annotation_no_warning() {
    let src = "val x: Option<Int> = None";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in type annotation"
    );
}

// === Nested Generics ===

#[test]
fn test_deprecated_nested_generics() {
    let src = "val x: List[Option[String]] = []";
    let count = count_deprecation_warnings(src);
    assert!(count >= 2, "Should warn about both nested [] usages (found {})", count);
}

#[test]
fn test_new_nested_generics_no_warning() {
    let src = "val x: List<Option<String>> = []";
    assert!(!has_deprecation_warning(src), "Should NOT warn about nested <> syntax");
}

// === Array Types (should NOT warn) ===

#[test]
fn test_array_type_no_warning() {
    let src = "val arr: [i32] = [1, 2, 3]";
    assert!(!has_deprecation_warning(src), "Should NOT warn about array type [i32]");
}

#[test]
fn test_fixed_array_type_no_warning() {
    let src = "val arr: [i32; 10] = []";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about fixed-size array [i32; 10]"
    );
}

// === Array Literals (should NOT warn) ===

#[test]
fn test_array_literal_no_warning() {
    let src = "val arr = [1, 2, 3, 4, 5]";
    assert!(!has_deprecation_warning(src), "Should NOT warn about array literal");
}

#[test]
fn test_empty_array_literal_no_warning() {
    let src = "val arr = []";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about empty array literal"
    );
}

// === String Literals (should NOT warn) ===

#[test]
fn test_string_with_bracket_syntax_no_warning() {
    let src = r#"val s = "This is List[T] in a string""#;
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about [] in string literal"
    );
}

// === Comments (should NOT warn) ===

#[test]
fn test_comment_with_bracket_syntax_no_warning() {
    let src = "# This is Option[T] in a comment\nval x = 42";
    assert!(!has_deprecation_warning(src), "Should NOT warn about [] in comment");
}

// === Multiple Warnings ===

#[test]
fn test_multiple_deprecations_in_same_file() {
    let src = r#"
fn map[T, U](list: List[T], f: fn(T) -> U) -> List[U]:
    []

struct Container[T]:
    value: T

val opt: Option[String] = None
"#;
    let count = count_deprecation_warnings(src);
    assert!(count >= 5, "Should have multiple warnings (found {})", count);
}

// === Class Generic Parameters ===

#[test]
fn test_deprecated_class_generic() {
    let src = "class MyClass[T]:\n    val data: T";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in class"
    );
}

#[test]
fn test_new_class_generic_no_warning() {
    let src = "class MyClass<T>:\n    val data: T";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in class"
    );
}

// === Enum Generic Parameters ===

#[test]
fn test_deprecated_enum_generic() {
    let src = "enum Result[T, E]:\n    Ok(T)\n    Err(E)";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in enum"
    );
}

#[test]
fn test_new_enum_generic_no_warning() {
    let src = "enum Result<T, E>:\n    Ok(T)\n    Err(E)";
    assert!(!has_deprecation_warning(src), "Should NOT warn about <> syntax in enum");
}

// === Trait Generic Parameters ===

#[test]
fn test_deprecated_trait_generic() {
    let src = "trait Iterator[T]:\n    fn next() -> Option[T]";
    let count = count_deprecation_warnings(src);
    assert!(
        count >= 1,
        "Should warn about deprecated [] syntax in trait (found {})",
        count
    );
}

#[test]
fn test_new_trait_generic_no_warning() {
    let src = "trait Iterator<T>:\n    fn next() -> Option<T>";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in trait"
    );
}

// === Function Return Types ===

#[test]
fn test_deprecated_return_type() {
    let src = "fn get() -> Option[Int]:\n    None";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax in return type"
    );
}

#[test]
fn test_new_return_type_no_warning() {
    let src = "fn get() -> Option<Int>:\n    None";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax in return type"
    );
}

// === Const Generic Parameters ===

#[test]
fn test_deprecated_const_generic() {
    let src = "struct Array[T, const N: usize]:\n    data: [T; N]";
    assert!(
        has_deprecation_warning(src),
        "Should warn about deprecated [] syntax with const generics"
    );
}

#[test]
fn test_new_const_generic_no_warning() {
    let src = "struct Array<T, const N: usize>:\n    data: [T; N]";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about <> syntax with const generics"
    );
}

// === Edge Cases ===

#[test]
fn test_mixed_syntax() {
    // Test each function separately to isolate the issue
    let src_old = "fn legacy[T](x: T) -> T:\n    x";
    let src_new = "fn modern<U>(y: U) -> U:\n    y";

    // Old syntax should warn
    assert!(has_deprecation_warning(src_old), "Old syntax should warn");

    // New syntax should not warn
    assert!(!has_deprecation_warning(src_new), "New syntax should not warn");
}

#[test]
fn test_impl_block_with_generics() {
    let src = "impl[T] Container[T]:\n    fn new(val: T) -> Container[T]:\n        pass";
    let count = count_deprecation_warnings(src);
    assert!(count >= 2, "Should warn about [] in impl block (found {})", count);
}

#[test]
fn test_impl_block_with_new_syntax_no_warning() {
    let src = "impl<T> Container<T>:\n    fn new(val: T) -> Container<T>:\n        pass";
    assert!(!has_deprecation_warning(src), "Should NOT warn about <> in impl block");
}
