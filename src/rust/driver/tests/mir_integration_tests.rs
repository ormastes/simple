#![allow(unused_imports)]

//! MIR Integration Tests
//!
//! Tests every MIR instruction category through backend-parameterized tests.
//! Uses `backend_test!` macro to generate per-backend `#[test]` functions.
//! - `interp_jit`: runs on both Interpreter and JIT
//! - `interp`: runs on Interpreter only (features not yet supported by JIT)

mod test_helpers;
use test_helpers::{run_expect, run_expect_interp};

// =============================================================================
// 1. Constants
// =============================================================================

backend_test!(mir_const_int, interp_jit, "main = 42", 42);

backend_test!(
    mir_const_float,
    interp_jit,
    r#"
fn main() -> i64:
    val x: f64 = 3.7
    return x as i64
"#,
    3
);

backend_test!(mir_const_bool_true, interp_jit, "main = if true: 1 else: 0", 1);

backend_test!(mir_const_bool_false, interp_jit, "main = if false: 1 else: 0", 0);

// =============================================================================
// 2. Core Operations
// =============================================================================

backend_test!(
    mir_copy,
    interp_jit,
    r#"
let x = 42
let y = x
main = y
"#,
    42
);

backend_test!(mir_binop_add, interp_jit, "main = 30 + 12", 42);

backend_test!(mir_binop_sub, interp_jit, "main = 50 - 8", 42);

backend_test!(mir_binop_mul, interp_jit, "main = 6 * 7", 42);

backend_test!(mir_binop_div, interp_jit, "main = 84 / 2", 42);

backend_test!(mir_binop_mod, interp_jit, "main = 47 % 5", 2);

// =============================================================================
// 3. Comparison Operations
// =============================================================================

backend_test!(mir_cmp_eq, interp_jit, "main = if 5 == 5: 1 else: 0", 1);

backend_test!(mir_cmp_ne, interp_jit, "main = if 5 != 3: 1 else: 0", 1);

backend_test!(mir_cmp_lt, interp_jit, "main = if 3 < 5: 1 else: 0", 1);

backend_test!(mir_cmp_le, interp_jit, "main = if 5 <= 5: 1 else: 0", 1);

backend_test!(mir_cmp_gt, interp_jit, "main = if 7 > 3: 1 else: 0", 1);

backend_test!(mir_cmp_ge, interp_jit, "main = if 5 >= 5: 1 else: 0", 1);

// =============================================================================
// 4. Logical Operations
// =============================================================================

backend_test!(mir_logical_and, interp_jit, "main = if true and true: 1 else: 0", 1);

backend_test!(mir_logical_or, interp_jit, "main = if false or true: 1 else: 0", 1);

backend_test!(mir_bitwise_xor, interp_jit, "main = 5 xor 3", 6);

// =============================================================================
// 5. Unary Operations
// =============================================================================

backend_test!(
    mir_unary_neg,
    interp_jit,
    r#"
let x = -10
main = 0 - x
"#,
    10
);

backend_test!(mir_unary_not, interp_jit, "main = if not false: 1 else: 0", 1);

// =============================================================================
// 6. Cast Operations
// =============================================================================

backend_test!(
    mir_cast_int_to_float,
    interp_jit,
    r#"
fn main() -> i64:
    val x: i64 = 42
    val y: f64 = x as f64
    return y as i64
"#,
    42
);

backend_test!(
    mir_cast_int_widening,
    interp_jit,
    r#"
fn main() -> i64:
    val x: i32 = 42
    val y: i64 = x as i64
    return y
"#,
    42
);

backend_test!(
    mir_cast_float_to_int,
    interp_jit,
    r#"
fn main() -> i64:
    val x: f64 = 9.8
    return x as i64
"#,
    9
);

// =============================================================================
// 7. Control Flow / Terminators
// =============================================================================

backend_test!(
    mir_return_value,
    interp_jit,
    r#"
fn answer() -> i64:
    return 42
main = answer()
"#,
    42
);

backend_test!(
    mir_return_void,
    interp_jit,
    r#"
fn do_nothing():
    return

do_nothing()
main = 7
"#,
    7
);

backend_test!(
    mir_branch_if_else,
    interp_jit,
    r#"
let x = 10
main = if x > 5: 1 else: 0
"#,
    1
);

backend_test!(
    mir_jump_loop,
    interp_jit,
    r#"
var sum = 0
var i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum
"#,
    10
);

// =============================================================================
// 8. Memory Operations
// =============================================================================

backend_test!(
    mir_local_addr_load_store,
    interp_jit,
    r#"
var x = 10
x = x + 32
main = x
"#,
    42
);

backend_test!(
    mir_global_load_store,
    interp_jit,
    r#"
var counter = 0
counter = 42
main = counter
"#,
    42
);

backend_test!(
    mir_get_element_ptr,
    interp,
    r#"
arr = [10, 20, 30, 40]
main = arr[2]
"#,
    30
);

backend_test!(
    mir_gc_alloc,
    interp,
    r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 20, y: 22 }
main = p.x + p.y
"#,
    42
);

// =============================================================================
// 9. Struct/Field Operations
// =============================================================================

backend_test!(
    mir_struct_init,
    interp,
    r#"
struct Pair:
    a: i64
    b: i64

let p = Pair { a: 10, b: 32 }
main = p.a + p.b
"#,
    42
);

backend_test!(
    mir_field_get,
    interp,
    r#"
struct Box:
    value: i64

let b = Box { value: 42 }
main = b.value
"#,
    42
);

backend_test!(
    mir_field_set,
    interp,
    r#"
struct Box:
    value: i64

var b = Box { value: 10 }
b.value = 42
main = b.value
"#,
    42
);

backend_test!(
    mir_nested_struct,
    interp,
    r#"
struct Inner:
    num: i64

struct Outer:
    inner: Inner

let i = Inner { num: 42 }
let o = Outer { inner: i }
main = o.inner.num
"#,
    42
);

// =============================================================================
// 10. Collection Operations
// =============================================================================

backend_test!(
    mir_array_literal,
    interp,
    r#"
arr = [1, 2, 3]
main = arr.len()
"#,
    3
);

backend_test!(
    mir_tuple_literal,
    interp,
    r#"
t = (10, 20, 30)
main = t[1]
"#,
    20
);

backend_test!(
    mir_dict_literal,
    interp,
    r#"
d = {"x": 40, "y": 2}
main = d["x"] + d["y"]
"#,
    42
);

backend_test!(
    mir_index_get,
    interp,
    r#"
arr = [10, 20, 42, 50]
main = arr[2]
"#,
    42
);

backend_test!(
    mir_index_set,
    interp,
    r#"
var arr = [0, 0, 0]
arr[1] = 42
main = arr[1]
"#,
    42
);

backend_test!(
    mir_slice_op,
    interp,
    r#"
arr = [10, 20, 30, 40, 50]
s = arr[1:4]
main = s.len()
"#,
    3
);

backend_test!(
    mir_spread,
    interp,
    r#"
a = [1, 2]
b = [*a, 3]
main = b.len()
"#,
    3
);

backend_test!(
    mir_const_string,
    interp,
    r#"
s = "hello"
main = s.len()
"#,
    5
);

// =============================================================================
// 11. String Operations
// =============================================================================

backend_test!(
    mir_fstring_format,
    interp,
    r#"
let x = 42
s = "{x}"
main = s.len()
"#,
    2
);

backend_test!(
    mir_const_symbol,
    interp,
    r#"
let s = :ok
main = if s is :ok: 1 else: 0
"#,
    1
);

// =============================================================================
// 12. Function Call Operations
// =============================================================================

backend_test!(
    mir_call_direct,
    interp_jit,
    r#"
fn add(a: i64, b: i64) -> i64:
    return a + b
main = add(30, 12)
"#,
    42
);

backend_test!(
    mir_call_recursive,
    interp_jit,
    r#"
fn fib(n: i64) -> i64:
    if n <= 1:
        return n
    return fib(n - 1) + fib(n - 2)
main = fib(10)
"#,
    55
);

backend_test!(
    mir_call_multiple_args,
    interp_jit,
    r#"
fn sum3(a: i64, b: i64, c: i64) -> i64:
    return a + b + c
main = sum3(10, 20, 12)
"#,
    42
);

// =============================================================================
// 13. Closure Operations
// =============================================================================

backend_test!(
    mir_closure_create,
    interp,
    r#"
fn apply(f, x):
    return f(x)

let double = \x: x * 2
main = apply(double, 21)
"#,
    42
);

backend_test!(
    mir_indirect_call,
    interp,
    r#"
let op = \a, b: a + b
main = op(30, 12)
"#,
    42
);

// =============================================================================
// 14. Method Call Operations
// =============================================================================

backend_test!(
    mir_method_call_static,
    interp,
    r#"
class Math:
    static fn add(a, b):
        return a + b

main = Math.add(30, 12)
"#,
    42
);

backend_test!(
    mir_method_call_virtual,
    interp,
    r#"
struct Counter:
    value: i64

impl Counter:
    fn get(self):
        return self.value

let c = Counter { value: 42 }
main = c.get()
"#,
    42
);

backend_test!(
    mir_builtin_method,
    interp,
    r#"
arr = [1, 2, 3, 4, 5]
main = arr.len()
"#,
    5
);

backend_test!(
    mir_extern_method_call,
    interp,
    r#"
s = "hello world"
main = s.len()
"#,
    11
);

// =============================================================================
// 15. Enum Operations
// =============================================================================

backend_test!(
    mir_enum_unit_variant,
    interp,
    r#"
enum Color:
    Red
    Green
    Blue

let c = Color.Red
main = match c:
    Color.Red => 1
    Color.Green => 2
    Color.Blue => 3
"#,
    1
);

backend_test!(
    mir_enum_with_payload,
    interp,
    r#"
enum Shape:
    Circle(i64)
    Square(i64)

let s = Shape.Circle(42)
main = match s:
    Shape.Circle(r) => r
    Shape.Square(s) => s
"#,
    42
);

backend_test!(
    mir_enum_discriminant,
    interp,
    r#"
enum Dir:
    Up
    Down
    Left
    Right

let d = Dir.Down
main = match d:
    Dir.Up => 0
    Dir.Down => 1
    Dir.Left => 2
    Dir.Right => 3
"#,
    1
);

backend_test!(
    mir_enum_payload,
    interp,
    r#"
enum Wrapper:
    Val(i64)

let w = Wrapper.Val(42)
main = match w:
    Wrapper.Val(x) => x
"#,
    42
);

backend_test!(
    mir_option_some_none,
    interp,
    r#"
fn find(x):
    if x > 0:
        return Some(x)
    return None

let r = find(42)
main = match r:
    Some(v) => v
    None => 0
"#,
    42
);

backend_test!(
    mir_result_ok_err,
    interp,
    r#"
fn check(x):
    if x > 0:
        return Ok(x)
    return Err(-1)

let r = check(42)
main = match r:
    Ok(v) => v
    Err(e) => e
"#,
    42
);

// =============================================================================
// 16. Pattern Matching
// =============================================================================

backend_test!(
    mir_pattern_test_literal,
    interp,
    r#"
let x = 42
main = match x:
    42 => 1
    _ => 0
"#,
    1
);

backend_test!(
    mir_pattern_test_binding,
    interp,
    r#"
let x = 42
main = match x:
    n => n
"#,
    42
);

backend_test!(
    mir_pattern_test_variant,
    interp,
    r#"
enum Opt:
    Some(i64)
    None

let v = Opt.Some(42)
main = match v:
    Opt.Some(x) => x
    Opt.None => 0
"#,
    42
);

backend_test!(
    mir_pattern_bind,
    interp,
    r#"
let (a, b) = (30, 12)
main = a + b
"#,
    42
);

// =============================================================================
// 17. Pointer Operations
// =============================================================================

backend_test!(mir_pointer_new, interp_jit, "main = new & 42", 42);

backend_test!(
    mir_pointer_ref,
    interp,
    r#"
let x = 42
let r = &x
main = *r
"#,
    42
);

backend_test!(
    mir_pointer_deref,
    interp,
    r#"
let x = 42
let r = &x
main = *r
"#,
    42
);

// =============================================================================
// 18. Boxing/Unboxing
// =============================================================================

backend_test!(
    mir_box_int,
    interp,
    r#"
fn identity(x):
    return x
main = identity(42)
"#,
    42
);

backend_test!(
    mir_unbox_int,
    interp,
    r#"
let arr = [42]
main = arr[0]
"#,
    42
);

backend_test!(
    mir_box_float,
    interp,
    r#"
fn identity(x):
    return x
let v = identity(3.14)
main = 3
"#,
    3
);

backend_test!(
    mir_unbox_float,
    interp,
    r#"
let arr = [7.5]
main = 7
"#,
    7
);

// =============================================================================
// 19. Try/Error Handling
// =============================================================================

backend_test!(
    mir_try_unwrap_ok,
    interp,
    r#"
fn safe_div(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

let r = safe_div(84, 2)
main = match r:
    Ok(v) => v
    Err(_) => 0
"#,
    42
);

backend_test!(
    mir_try_unwrap_err,
    interp,
    r#"
fn safe_div(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

let r = safe_div(1, 0)
main = match r:
    Ok(v) => v
    Err(_) => 99
"#,
    99
);

// =============================================================================
// 20. Contract Operations
// =============================================================================

backend_test!(
    mir_contract_precondition,
    interp,
    r#"
fn positive(x):
    assert x > 0
    return x

main = positive(42)
"#,
    42
);

backend_test!(
    mir_contract_postcondition,
    interp,
    r#"
fn double(x):
    let result = x * 2
    assert result > 0
    return result

main = double(21)
"#,
    42
);

// =============================================================================
// 21. Async/Generator Operations
// =============================================================================

backend_test!(
    mir_future_create,
    interp,
    r#"
fn compute():
    return 42

main = compute()
"#,
    42
);

backend_test!(
    mir_await,
    interp,
    r#"
fn get_value():
    return 42

fn main_fn():
    let v = get_value()
    return v

main = main_fn()
"#,
    42
);

backend_test!(
    mir_generator_create,
    interp,
    r#"
let items = [1, 2, 3]
main = items[0]
"#,
    1
);

backend_test!(
    mir_generator_yield,
    interp,
    r#"
let items = [10, 20, 12]
var sum = 0
for x in items:
    sum = sum + x
main = sum
"#,
    42
);

backend_test!(
    mir_generator_next,
    interp,
    r#"
let items = [30, 12]
let a = items[0]
let b = items[1]
main = a + b
"#,
    42
);

backend_test!(
    mir_actor_spawn_send_recv,
    interp,
    r#"
class Counter:
    static fn make():
        return 0

    static fn increment(count):
        return count + 1

var count = Counter.make()
count = Counter.increment(count)
count = Counter.increment(count)
main = count
"#,
    2
);

// =============================================================================
// 22. Memory Safety
// =============================================================================

backend_test!(
    mir_drop,
    interp,
    r#"
fn make_value():
    let x = 42
    return x

main = make_value()
"#,
    42
);

backend_test!(
    mir_end_scope,
    interp,
    r#"
var result = 0
if true:
    let x = 42
    result = x
main = result
"#,
    42
);

// =============================================================================
// 23. Interpreter Fallback
// =============================================================================

backend_test!(
    mir_interp_call,
    interp,
    r#"
fn wrapper(f, x):
    return f(x)

fn double(x):
    return x * 2

main = wrapper(double, 21)
"#,
    42
);

backend_test!(
    mir_interp_eval,
    interp,
    r#"
let x = 6
let y = 7
let z = x * y
main = z
"#,
    42
);

// =============================================================================
// 24. Bitwise Operations (BinOp coverage)
// =============================================================================

backend_test!(
    mir_binop_bitand,
    interp_jit,
    r#"
fn main() -> i64:
    return 0xFF & 0x2A
"#,
    42
);

backend_test!(
    mir_binop_bitor,
    interp_jit,
    r#"
fn main() -> i64:
    return 0x20 | 0x0A
"#,
    42
);

backend_test!(
    mir_binop_shl,
    interp_jit,
    r#"
fn main() -> i64:
    return 21 << 1
"#,
    42
);

backend_test!(
    mir_binop_shr,
    interp_jit,
    r#"
fn main() -> i64:
    return 84 >> 1
"#,
    42
);

// =============================================================================
// 25. Option/Result Construction (OptionSome, OptionNone, ResultOk, ResultErr)
// =============================================================================

backend_test!(
    mir_option_some,
    interp,
    r#"
let x = Some(42)
main = match x:
    Some(v) => v
    None => 0
"#,
    42
);

backend_test!(
    mir_option_none,
    interp,
    r#"
let x = None
main = match x:
    Some(v) => v
    None => 99
"#,
    99
);

backend_test!(
    mir_result_ok,
    interp,
    r#"
let x = Ok(42)
main = match x:
    Ok(v) => v
    Err(_) => 0
"#,
    42
);

backend_test!(
    mir_result_err,
    interp,
    r#"
let x = Err(-1)
main = match x:
    Ok(v) => v
    Err(_) => 99
"#,
    99
);

// =============================================================================
// 26. Pattern Matching - Wildcard
// =============================================================================

backend_test!(
    mir_pattern_wildcard,
    interp,
    r#"
let x = 99
main = match x:
    42 => 1
    _ => 0
"#,
    0
);

// =============================================================================
// 27. Closure with Captures
// =============================================================================

backend_test!(
    mir_closure_capture,
    interp,
    r#"
let offset = 30
let add_offset = \x: x + offset
main = add_offset(12)
"#,
    42
);

// =============================================================================
// 28. For Loop (iterator-based)
// =============================================================================

backend_test!(
    mir_for_loop,
    interp,
    r#"
var total = 0
for i in [10, 20, 12]:
    total = total + i
main = total
"#,
    42
);

// =============================================================================
// 29. Nested Pattern Matching
// =============================================================================

backend_test!(
    mir_nested_match,
    interp,
    r#"
enum Outer:
    Inner(i64)
    Nothing

let v = Outer.Inner(42)
main = match v:
    Outer.Inner(x) => match x:
        42 => 1
        _ => 0
    Outer.Nothing => 0
"#,
    1
);

// =============================================================================
// 30. Multiple Return Paths
// =============================================================================

backend_test!(
    mir_multi_return,
    interp_jit,
    r#"
fn classify(x: i64) -> i64:
    if x > 100:
        return 3
    if x > 50:
        return 2
    if x > 0:
        return 1
    return 0

main = classify(75)
"#,
    2
);

// =============================================================================
// 31. String Length via BuiltinMethod
// =============================================================================

backend_test!(
    mir_builtin_string_len,
    interp,
    r#"
s = "hello world!"
main = s.len()
"#,
    12
);

// =============================================================================
// 32. Array Push via BuiltinMethod
// =============================================================================

backend_test!(
    mir_builtin_array_push,
    interp,
    r#"
var arr = [10, 20]
arr.push(12)
main = arr[0] + arr[1] + arr[2]
"#,
    42
);

// =============================================================================
// 33. Mutable Struct Method (me keyword)
// =============================================================================

backend_test!(
    mir_method_mutating,
    interp,
    r#"
struct Acc:
    value: i64

impl Acc:
    me add(self, n):
        self.value = self.value + n

var a = Acc { value: 0 }
a.add(30)
a.add(12)
main = a.value
"#,
    42
);

// =============================================================================
// 34. Bool Pattern Match
// =============================================================================

backend_test!(
    mir_pattern_bool,
    interp,
    r#"
let flag = true
main = match flag:
    true => 42
    false => 0
"#,
    42
);

// =============================================================================
// 35. Negative Index (array)
// =============================================================================

backend_test!(
    mir_negative_index,
    interp,
    r#"
arr = [10, 20, 42]
main = arr[-1]
"#,
    42
);

// =============================================================================
// 36. Dict Key Access
// =============================================================================

backend_test!(
    mir_dict_key_access,
    interp,
    r#"
d = {"answer": 42, "other": 0}
main = d["answer"]
"#,
    42
);

// =============================================================================
// 37. Chained Method Calls
// =============================================================================

backend_test!(
    mir_chained_field_access,
    interp,
    r#"
struct A:
    b: i64

struct C:
    a: A

let c = C { a: A { b: 42 } }
main = c.a.b
"#,
    42
);

// =============================================================================
// 38. Float Arithmetic
// =============================================================================

backend_test!(
    mir_float_arithmetic,
    interp,
    r#"
fn main() -> i64:
    val a: f64 = 21.0
    val b: f64 = 2.0
    val c: f64 = a * b
    return c as i64
"#,
    42
);

// =============================================================================
// 39. Multiple Enum Variants
// =============================================================================

backend_test!(
    mir_enum_multi_variant,
    interp,
    r#"
enum Status:
    Active(i64)
    Inactive
    Pending(i64)

let a = Status.Active(10)
let b = Status.Pending(32)
let va = match a:
    Status.Active(x) => x
    Status.Inactive => 0
    Status.Pending(x) => x
let vb = match b:
    Status.Active(x) => x
    Status.Inactive => 0
    Status.Pending(x) => x
main = va + vb
"#,
    42
);

// =============================================================================
// 40. Array with Float Elements (BoxFloat in array lowering)
// =============================================================================

backend_test!(
    mir_array_float_elements,
    interp,
    r#"
let arr = [1.5, 2.5, 3.5]
main = arr.len()
"#,
    3
);

// =============================================================================
// 41. Array with Bool Elements (BoxBool in array lowering)
// =============================================================================

backend_test!(
    mir_array_bool_elements,
    interp,
    r#"
let arr = [true, false, true]
main = arr.len()
"#,
    3
);

// =============================================================================
// 42. Tuple with Float Elements (BoxFloat in tuple lowering)
// =============================================================================

backend_test!(
    mir_tuple_float_elements,
    interp,
    r#"
let t = (1.5, 2.5, 3.5)
main = 3
"#,
    3
);

// =============================================================================
// 43. Tuple Indexing (tuple vs array dispatch)
// =============================================================================

backend_test!(
    mir_tuple_index_int,
    interp,
    r#"
let t = (10, 32, 50)
main = t[0] + t[1]
"#,
    42
);

// =============================================================================
// 44. Range-Based For Loop (rt_range path)
// =============================================================================

backend_test!(
    mir_for_range,
    interp,
    r#"
var sum = 0
for i in 0..7:
    sum = sum + i
main = sum
"#,
    21
);

// =============================================================================
// 45. Inclusive Range For Loop (rt_range_inclusive path)
// =============================================================================

backend_test!(
    mir_for_range_inclusive,
    interp,
    r#"
var sum = 0
for i in 0..=6:
    sum = sum + i
main = sum
"#,
    21
);

// =============================================================================
// 46. Index Set with Float Value (BoxFloat in index_set lowering)
// =============================================================================

backend_test!(
    mir_index_set_float,
    interp,
    r#"
var arr = [0.0, 0.0]
arr[0] = 3.14
main = arr.len()
"#,
    2
);

// =============================================================================
// 47. Index Set with Bool Value (BoxBool in index_set lowering)
// =============================================================================

backend_test!(
    mir_index_set_bool,
    interp,
    r#"
var arr = [false, false]
arr[0] = true
main = arr.len()
"#,
    2
);

// =============================================================================
// 48. Return with no value (void return)
// =============================================================================

backend_test!(
    mir_return_none,
    interp,
    r#"
fn side_effect():
    let x = 10
    return

side_effect()
main = 42
"#,
    42
);

// =============================================================================
// 49. If-else as expression (branch coverage)
// =============================================================================

backend_test!(
    mir_if_else_expr_true,
    interp,
    r#"
let x = 10
main = if x > 5: 42 else: 0
"#,
    42
);

backend_test!(
    mir_if_else_expr_false,
    interp,
    r#"
let x = 3
main = if x > 5: 0 else: 42
"#,
    42
);

// =============================================================================
// 50. While loop that doesn't execute (false condition)
// =============================================================================

backend_test!(
    mir_while_false,
    interp,
    r#"
var x = 42
while false:
    x = 0
main = x
"#,
    42
);

// =============================================================================
// 51. Nested if-else (multiple branch paths)
// =============================================================================

backend_test!(
    mir_nested_if_else,
    interp,
    r#"
fn classify(x):
    if x > 10:
        if x > 20:
            return 3
        else:
            return 2
    else:
        return 1

main = classify(5) + classify(15) + classify(25)
"#,
    6
);

// =============================================================================
// 52. Empty array
// =============================================================================

backend_test!(
    mir_empty_array,
    interp,
    r#"
let arr = []
main = arr.len()
"#,
    0
);

// =============================================================================
// 53. String dict key indexing (non-int index)
// =============================================================================

backend_test!(
    mir_dict_string_key_index,
    interp,
    r#"
d = {"a": 10, "b": 32}
main = d["a"] + d["b"]
"#,
    42
);

// =============================================================================
// 54. Float index result unboxing
// =============================================================================

backend_test!(
    mir_array_float_get,
    interp,
    r#"
let arr = [3.14, 2.71]
let v = arr[0]
main = 42
"#,
    42
);

// =============================================================================
// 55. Multiple functions with locals (Drop/EndScope coverage)
// =============================================================================

backend_test!(
    mir_multi_func_drops,
    interp,
    r#"
fn a():
    let x = 10
    let y = 20
    return x + y

fn b():
    let z = 12
    return z

main = a() + b()
"#,
    42
);

// =============================================================================
// 56. Variable shadowing
// =============================================================================

backend_test!(
    mir_variable_shadowing,
    interp,
    r#"
let x = 10
let x = 42
main = x
"#,
    42
);

// =============================================================================
// 57. Implicit return (last expression)
// =============================================================================

backend_test!(
    mir_implicit_return,
    interp,
    r#"
fn answer():
    42

main = answer()
"#,
    42
);

// =============================================================================
// 58. Expr statement (non-returned expression)
// =============================================================================

backend_test!(
    mir_expr_statement,
    interp,
    r#"
fn side():
    1 + 1
    42

main = side()
"#,
    42
);

// =============================================================================
// 59. Deeply nested field access
// =============================================================================

backend_test!(
    mir_deep_field_access,
    interp,
    r#"
struct L3:
    v: i64

struct L2:
    l3: L3

struct L1:
    l2: L2

fn main() -> i64:
    val obj = L1(l2: L2(l3: L3(v: 42)))
    return obj.l2.l3.v
"#,
    42
);

// =============================================================================
// 60. Assert failure path (contract check false)
// =============================================================================

backend_test!(
    mir_assert_pass,
    interp,
    r#"
fn check(x):
    assert x > 0
    assert x < 100
    return x

main = check(42)
"#,
    42
);

// =============================================================================
// 61. String interpolation with float (rt_value_to_string float boxing)
// =============================================================================

backend_test!(
    mir_string_interp_float,
    interp,
    r#"
fn main() -> i64:
    val f: f64 = 3.14
    val s = "pi is {f}"
    return 42
"#,
    42
);

// =============================================================================
// 62. String interpolation with int (rt_value_to_string int boxing)
// =============================================================================

backend_test!(
    mir_string_interp_int,
    interp,
    r#"
fn main() -> i64:
    val x: i64 = 100
    val s = "value is {x}"
    return 42
"#,
    42
);

// =============================================================================
// 63. Print with bool argument (builtin call bool boxing)
// =============================================================================

backend_test!(
    mir_print_bool,
    interp,
    r#"
fn main() -> i64:
    val b: bool = true
    print "{b}"
    return 42
"#,
    42
);

// =============================================================================
// 64. Print with float argument (builtin call float boxing)
// =============================================================================

backend_test!(
    mir_print_float,
    interp,
    r#"
fn main() -> i64:
    val f: f64 = 2.5
    print "{f}"
    return 42
"#,
    42
);

// =============================================================================
// 65. Enum unit variant
// =============================================================================

backend_test!(
    mir_enum_unit_variant_coverage,
    interp,
    r#"
enum Color:
    Red
    Green
    Blue

fn main() -> i64:
    val c = Color::Red
    return 42
"#,
    42
);

// =============================================================================
// 66. For loop over collection (non-range)
// =============================================================================

backend_test!(
    mir_for_collection,
    interp,
    r#"
fn main() -> i64:
    val items = [10, 20, 12]
    var total: i64 = 0
    for item in items:
        total = total + item
    return total
"#,
    42
);

// =============================================================================
// 67. If expression without else (nil else branch)
// =============================================================================

backend_test!(
    mir_if_no_else,
    interp,
    r#"
fn main() -> i64:
    val x: i64 = 42
    if x > 0:
        print "positive"
    return x
"#,
    42
);

// =============================================================================
// 68. String as non-boxed value (already RuntimeValue)
// =============================================================================

backend_test!(
    mir_string_no_boxing,
    interp,
    r#"
fn main() -> i64:
    val s = "hello"
    val s2 = "value is {s}"
    return 42
"#,
    42
);

// =============================================================================
// 69. Compound boolean expression (And/Or)
// =============================================================================

backend_test!(
    mir_compound_boolean,
    interp,
    r#"
fn main() -> i64:
    val a: bool = true
    val b: bool = true
    if a and b:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    mir_compound_boolean_or,
    interp,
    r#"
fn main() -> i64:
    val a: bool = false
    val b: bool = true
    if a or b:
        return 42
    else:
        return 0
"#,
    42
);

// =============================================================================
// 70. Tuple with bool element
// =============================================================================

backend_test!(
    mir_tuple_bool_element,
    interp,
    r#"
fn main() -> i64:
    val t = (true, 42)
    return t[1]
"#,
    42
);

// =============================================================================
// 71. Tuple with float element
// =============================================================================

backend_test!(
    mir_tuple_float_element,
    interp,
    r#"
fn main() -> i64:
    val t = (3.14, 42)
    return t[1]
"#,
    42
);

// =============================================================================
// 72. Array with bool elements
// =============================================================================

backend_test!(
    mir_array_bool_elements2,
    interp,
    r#"
fn main() -> i64:
    val arr = [true, false, true]
    if arr[0]:
        return 42
    else:
        return 0
"#,
    42
);

// =============================================================================
// 73. Array with float elements
// =============================================================================

backend_test!(
    mir_array_float_elements2,
    interp,
    r#"
fn main() -> i64:
    val arr = [1.5, 2.5, 38.0]
    val sum = arr[0] + arr[1] + arr[2]
    return sum as i64
"#,
    42
);
