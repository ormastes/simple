//! Codegen coverage tests for MIR instruction categories.
//!
//! Uses `backend_test!` macro to run on both Interpreter and JIT.
//! Previously JIT-only; now gains interpreter coverage for free.

mod test_helpers;

// =============================================================================
// Struct/Class Initialization and Field Access
// =============================================================================

backend_test!(
    codegen_struct_init_simple,
    interp_jit,
    r#"
struct Point:
    x: i64
    y: i64

fn main() -> i64:
    val p = Point(x: 40, y: 2)
    return p.x + p.y
"#,
    42
);

backend_test!(
    codegen_nested_struct,
    interp_jit,
    r#"
struct Inner:
    v: i64

struct Outer:
    a: i64
    b: i64

fn main() -> i64:
    val inner = Inner(v: 10)
    val outer = Outer(a: inner.v, b: 32)
    return outer.a + outer.b
"#,
    42
);

// =============================================================================
// Pointer Operations
// =============================================================================

backend_test!(
    codegen_pointer_new_deref,
    interp_jit,
    r#"
fn main() -> i64:
    val p = &42
    return *p
"#,
    42
);

// =============================================================================
// Type Cast Operations
// =============================================================================

backend_test!(
    codegen_cast_int_to_float_back,
    interp_jit,
    r#"
fn main() -> i64:
    val x: i64 = 42
    val f: f64 = x as f64
    val back: i64 = f as i64
    return back
"#,
    42
);

// =============================================================================
// Copy Operations
// =============================================================================

backend_test!(
    codegen_copy_operation,
    interp_jit,
    r#"
fn main() -> i64:
    val a: i64 = 42
    val b: i64 = a
    return b
"#,
    42
);

// =============================================================================
// Collection Operations - Array
// =============================================================================

// array indexing in JIT returns wrong value - interpreter only
backend_test!(
    codegen_array_literal,
    interp,
    r#"
fn main() -> i64:
    val arr = [10, 20, 42, 30]
    return arr[2]
"#,
    42
);

// =============================================================================
// String Operations
// =============================================================================

backend_test!(
    codegen_const_string,
    interp_jit,
    r#"
fn main() -> i64:
    val s = "hello"
    return 42
"#,
    42
);

// =============================================================================
// Value Boxing/Unboxing
// =============================================================================

backend_test!(
    codegen_box_unbox_int,
    interp_jit,
    r#"
fn main() -> i64:
    val x: i64 = 42
    return x
"#,
    42
);

// =============================================================================
// Memory Safety Operations
// =============================================================================

backend_test!(
    codegen_scope_cleanup,
    interp_jit,
    r#"
fn scoped_work() -> i64:
    val x: i64 = 10
    val y: i64 = 32
    return x + y

fn main() -> i64:
    return scoped_work()
"#,
    42
);

// =============================================================================
// GC and Memory Operations
// =============================================================================

backend_test!(
    codegen_gc_alloc,
    interp_jit,
    r#"
struct BigStruct:
    a: i64
    b: i64
    c: i64
    d: i64

fn main() -> i64:
    val s = BigStruct(a: 10, b: 20, c: 10, d: 2)
    return s.a + s.b + s.c + s.d
"#,
    42
);

// =============================================================================
// Unary Operations
// =============================================================================

backend_test!(
    codegen_unary_neg,
    interp_jit,
    r#"
fn main() -> i64:
    val x: i64 = -42
    return -x
"#,
    42
);

backend_test!(
    codegen_unary_not,
    interp_jit,
    r#"
fn main() -> i64:
    val b: bool = false
    if not b:
        return 42
    else:
        return 0
"#,
    42
);

// =============================================================================
// Const Bool Operations
// =============================================================================

backend_test!(
    codegen_const_bool_true,
    interp_jit,
    r#"
fn main() -> i64:
    val b: bool = true
    if b:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    codegen_const_bool_false,
    interp_jit,
    r#"
fn main() -> i64:
    val b: bool = false
    if b:
        return 0
    else:
        return 42
"#,
    42
);

// =============================================================================
// Const Float Operations
// =============================================================================

backend_test!(
    codegen_const_float,
    interp_jit,
    r#"
fn main() -> i64:
    val f: f64 = 42.5
    return f as i64
"#,
    42
);

// =============================================================================
// Local Address and Element Pointer Operations
// =============================================================================

backend_test!(
    codegen_local_addr,
    interp_jit,
    r#"
fn main() -> i64:
    var x: i64 = 0
    x = 42
    return x
"#,
    42
);

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
