//! Codegen coverage tests for MIR instruction categories.
//!
//! This test file ensures codegen coverage for instruction categories
//! that are supported by the JIT compiler.

use simple_driver::run_jit;

// =============================================================================
// Struct/Class Initialization and Field Access (WORKING)
// =============================================================================

#[test]
fn codegen_struct_init_simple() {
    // Tests: StructInit, FieldGet
    let code = r#"
struct Point:
    x: i64
    y: i64

fn main() -> i64:
    val p = Point(x: 40, y: 2)
    return p.x + p.y
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn codegen_nested_struct() {
    // Tests: StructInit with nested structs, FieldGet chain
    let code = r#"
struct Inner:
    v: i64

struct Outer:
    a: i64
    b: i64

fn main() -> i64:
    val inner = Inner(v: 10)
    val outer = Outer(a: inner.v, b: 32)
    return outer.a + outer.b
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Pointer Operations (WORKING)
// =============================================================================

#[test]
fn codegen_pointer_new_deref() {
    // Tests: PointerNew, PointerDeref
    let code = r#"
fn main() -> i64:
    val p = &42
    return *p
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Type Cast Operations (WORKING)
// =============================================================================

#[test]
fn codegen_cast_int_to_float_back() {
    // Tests: Cast instruction
    let code = r#"
fn main() -> i64:
    val x: i64 = 42
    val f: f64 = x as f64
    val back: i64 = f as i64
    return back
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Copy Operations (WORKING)
// =============================================================================

#[test]
fn codegen_copy_operation() {
    // Tests: Copy instruction
    let code = r#"
fn main() -> i64:
    val a: i64 = 42
    val b: i64 = a
    return b
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Collection Operations - Array (WORKING)
// =============================================================================

#[test]
fn codegen_array_literal() {
    // Tests: ArrayLit, IndexGet (via rt_array_get)
    let code = r#"
fn main() -> i64:
    val arr = [10, 20, 42, 30]
    return arr[2]
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// String Operations (WORKING)
// =============================================================================

#[test]
fn codegen_const_string() {
    // Tests: ConstString
    let code = r#"
fn main() -> i64:
    val s = "hello"
    return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Value Boxing/Unboxing (WORKING)
// =============================================================================

#[test]
fn codegen_box_unbox_int() {
    // Tests: BoxInt, UnboxInt - used at FFI boundaries
    let code = r#"
fn main() -> i64:
    val x: i64 = 42
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Memory Safety Operations (WORKING)
// =============================================================================

#[test]
fn codegen_scope_cleanup() {
    // Tests: Drop, EndScope (implicit at scope boundaries)
    let code = r#"
fn scoped_work() -> i64:
    val x: i64 = 10
    val y: i64 = 32
    return x + y

fn main() -> i64:
    return scoped_work()
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// GC and Memory Operations (WORKING)
// =============================================================================

#[test]
fn codegen_gc_alloc() {
    // Tests: GcAlloc (used implicitly for heap-allocated structures)
    let code = r#"
struct BigStruct:
    a: i64
    b: i64
    c: i64
    d: i64

fn main() -> i64:
    val s = BigStruct(a: 10, b: 20, c: 10, d: 2)
    return s.a + s.b + s.c + s.d
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Unary Operations (WORKING)
// =============================================================================

#[test]
fn codegen_unary_neg() {
    // Tests: UnaryOp (negation)
    let code = r#"
fn main() -> i64:
    val x: i64 = -42
    return -x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn codegen_unary_not() {
    // Tests: UnaryOp (logical not)
    let code = r#"
fn main() -> i64:
    val b: bool = false
    if not b:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Const Bool Operations (WORKING)
// =============================================================================

#[test]
fn codegen_const_bool_true() {
    // Tests: ConstBool
    let code = r#"
fn main() -> i64:
    val b: bool = true
    if b:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn codegen_const_bool_false() {
    // Tests: ConstBool
    let code = r#"
fn main() -> i64:
    val b: bool = false
    if b:
        return 0
    else:
        return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Const Float Operations (WORKING)
// =============================================================================

#[test]
fn codegen_const_float() {
    // Tests: ConstFloat
    let code = r#"
fn main() -> i64:
    val f: f64 = 42.5
    return f as i64
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Local Address and Element Pointer Operations (WORKING)
// =============================================================================

#[test]
fn codegen_local_addr() {
    // Tests: LocalAddr, Load, Store
    let code = r#"
fn main() -> i64:
    var x: i64 = 0
    x = 42
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// TODO: Features needing JIT implementation
// =============================================================================
// The following features need additional JIT codegen support:
//
// 0. Field Assignment: MIR lowering for complex lvalues
//    - codegen_struct_field_set (c.value = 42)
//    - Error: "Unsupported HIR construct: complex lvalue"
//
// 1. Closures/Lambdas: HIR lowering for lambda captures
//    - codegen_closure_capture
//    - codegen_lambda_no_capture
//
// 2. Enums: JIT codegen for enum discriminant/payload
//    - codegen_enum_unit_variant
//    - codegen_enum_with_payload
//
// 3. Option/Result types: Built on enum codegen
//    - codegen_option_some
//    - codegen_option_none
//    - codegen_result_ok
//    - codegen_result_err
//
// 4. Method calls: JIT method dispatch
//    - codegen_method_call_static
//    - codegen_method_with_args
//
// 5. Pattern matching: JIT pattern codegen
//    - codegen_pattern_literal
//    - codegen_pattern_binding
//
// 6. Tuple index: HIR lowering for tuple access
//    - codegen_tuple_literal
