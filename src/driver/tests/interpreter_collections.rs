//! Interpreter tests - collections

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_array_literal() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
main = arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_array_len() {
    let code = r#"
arr = [10, 20, 30]
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_array_first_last() {
    let code = r#"
arr = [5, 10, 15, 20]
main = arr.first() + arr.last()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 25); // 5 + 20
}

#[test]
fn interpreter_array_contains() {
    let code = r#"
arr = [1, 2, 3]
main = if arr.contains(2): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_array_is_empty() {
    let code = r#"
arr = []
main = if arr.is_empty(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Tuple Tests =============

#[test]
fn interpreter_tuple_literal() {
    let code = r#"
t = (10, 20, 30)
main = t[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_tuple_len() {
    let code = r#"
t = (1, 2, 3, 4)
main = t.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_tuple_destructure() {
    let code = r#"
let (a, b, c) = (10, 20, 30)
main = a + b + c
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

// ============= Dictionary Tests =============

#[test]
fn interpreter_dict_literal() {
    let code = r#"
d = {"a": 10, "b": 20}
main = d["a"] + d["b"]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_dict_len() {
    let code = r#"
d = {"x": 1, "y": 2, "z": 3}
main = d.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_dict_contains_key() {
    let code = r#"
d = {"name": 42}
main = if d.contains_key("name"): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_dict_get() {
    let code = r#"
d = {"value": 99}
main = d.get("value")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

// ============= Const/Static Tests =============

#[test]
fn interpreter_string_len() {
    let code = r#"
s = "hello"
main = s.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_string_contains() {
    let code = r#"
s = "hello world"
main = if s.contains("world"): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_string_index() {
    // String indexing returns single character
    let code = r#"
s = "abc"
main = if s[1] == "b": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Pattern Matching with Collections =============

#[test]
fn interpreter_array_push() {
    let code = r#"
arr = [1, 2, 3]
arr = arr.push(4)
main = arr[3]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_array_concat() {
    let code = r#"
a = [1, 2]
b = [3, 4]
c = a.concat(b)
main = c.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_array_slice() {
    let code = r#"
arr = [0, 1, 2, 3, 4, 5]
sliced = arr.slice(2, 5)
main = sliced.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_array_map() {
    let code = r#"
arr = [1, 2, 3]
doubled = arr.map(\x: x * 2)
main = doubled[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_array_filter() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
evens = arr.filter(\x: x % 2 == 0)
main = evens.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_array_reduce() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
sum = arr.reduce(0, \acc, x: acc + x)
main = sum
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_array_any_all() {
    let code = r#"
arr = [2, 4, 6]
all_even = arr.all(\x: x % 2 == 0)
main = if all_even: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_array_join() {
    let code = r#"
arr = [1, 2, 3]
s = arr.join("-")
main = if s == "1-2-3": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_array_sum() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
main = arr.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_array_reverse() {
    let code = r#"
arr = [1, 2, 3]
rev = arr.reverse()
main = rev[0]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

// ============= Dict Functional Methods =============

#[test]
fn interpreter_dict_set() {
    let code = r#"
d = {"a": 1}
d = d.set("b", 2)
main = d["b"]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_dict_remove() {
    let code = r#"
d = {"a": 1, "b": 2}
d = d.remove("a")
main = d.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_dict_merge() {
    let code = r#"
d1 = {"a": 1}
d2 = {"b": 2}
d = d1.merge(d2)
main = d.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_dict_get_or() {
    let code = r#"
d = {"a": 10}
main = d.get_or("b", 99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

// ============= Functional Update Operator (->)  =============

// ============= List Comprehension =============

#[test]
fn interpreter_list_comprehension_basic() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
doubled = [x * 2 for x in arr]
main = doubled[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6); // 3 * 2
}

#[test]
fn interpreter_list_comprehension_with_condition() {
    let code = r#"
arr = [1, 2, 3, 4, 5, 6]
evens = [x for x in arr if x % 2 == 0]
main = evens.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // [2, 4, 6]
}

#[test]
fn interpreter_list_comprehension_squares() {
    let code = r#"
squares = [x * x for x in [1, 2, 3, 4]]
main = squares[3]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 16); // 4 * 4
}

// ============= Dict Comprehension =============

#[test]
fn interpreter_dict_comprehension_basic() {
    let code = r#"
arr = [1, 2, 3]
d = {x: x * x for x in arr}
main = d[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

// ============= Slicing =============

#[test]
fn interpreter_slice_basic() {
    let code = r#"
arr = [0, 1, 2, 3, 4, 5]
sub = arr[1:4]
main = sub.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // [1, 2, 3]
}

#[test]
fn interpreter_slice_start_only() {
    let code = r#"
arr = [0, 1, 2, 3, 4]
sub = arr[2:]
main = sub[0]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_slice_end_only() {
    let code = r#"
arr = [0, 1, 2, 3, 4]
sub = arr[:3]
main = sub.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // [0, 1, 2]
}

#[test]
fn interpreter_slice_with_step() {
    let code = r#"
arr = [0, 1, 2, 3, 4, 5, 6, 7]
evens = arr[::2]
main = evens.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4); // [0, 2, 4, 6]
}

// ============= Negative Indexing =============

#[test]
fn interpreter_negative_index_array() {
    let code = r#"
arr = [10, 20, 30, 40, 50]
main = arr[-1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_negative_index_second_from_end() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
main = arr[-2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_negative_index_string() {
    let code = r#"
s = "hello"
c = s[-1]
main = if c == "o": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Spread Operators =============

#[test]
fn interpreter_array_spread() {
    let code = r#"
a = [1, 2, 3]
b = [4, 5]
c = [*a, *b]
main = c.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_array_spread_mixed() {
    let code = r#"
a = [2, 3]
arr = [1, *a, 4]
main = arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

// ============= Tuple Unpacking =============

#[test]
fn interpreter_tuple_unpacking_basic() {
    let code = r#"
let (x, y) = (1, 2)
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_tuple_unpacking_swap() {
    let code = r#"
a = 10
b = 20
let (x, y) = (b, a)
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_tuple_unpacking_from_array() {
    let code = r#"
arr = [5, 10, 15]
let (first, second, third) = arr
main = second
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

// ============= Chained Comparisons =============

#[test]
fn interpreter_chained_comparison_basic() {
    let code = r#"
x = 5
main = if 0 < x < 10: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_chained_comparison_false() {
    let code = r#"
x = 15
main = if 0 < x < 10: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_chained_comparison_three_way() {
    let code = r#"
a = 1
b = 5
c = 10
main = if a < b < c: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_chained_comparison_mixed() {
    let code = r#"
x = 5
main = if 0 <= x <= 10: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Context Managers (with) =============

#[test]
fn interpreter_with_basic() {
    // Basic with statement - just executes body
    let code = r#"
counter = 0
with 42:
    counter = 1
main = counter
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_with_as_binding() {
    // With statement binds resource to name
    let code = r#"
with 42 as x:
    result = x + 1
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 43);
}

#[test]
fn interpreter_with_class_enter_exit() {
    // Context manager with __enter__ and __exit__ methods
    // Simplified test that returns value from __enter__
    let code = r#"
class Resource:
    value: i64 = 0

    fn __enter__(self):
        return self.value + 10

    fn __exit__(self):
        return 0

r = Resource { value: 5 }
with r as v:
    result = v

main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    // __enter__ returns self.value + 10 = 5 + 10 = 15
    assert_eq!(result.exit_code, 15);
}

// ============= Decorators =============

#[test]
fn interpreter_decorator_basic() {
    // Basic decorator that wraps a function
    let code = r#"
fn double_result(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@double_result
fn add_one(x):
    return x + 1

main = add_one(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    // add_one(5) = 6, then doubled = 12
    assert_eq!(result.exit_code, 12);
}

#[test]
fn interpreter_decorator_with_args() {
    // Decorator factory that takes arguments
    let code = r#"
fn multiply_by(factor):
    fn decorator(f):
        fn wrapper(x):
            return f(x) * factor
        return wrapper
    return decorator

@multiply_by(3)
fn increment(x):
    return x + 1

main = increment(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    // increment(10) = 11, then * 3 = 33
    assert_eq!(result.exit_code, 33);
}

#[test]
fn interpreter_multiple_decorators() {
    // Multiple decorators stacked
    let code = r#"
fn add_ten(f):
    fn wrapper(x):
        return f(x) + 10
    return wrapper

fn double(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@add_ten
@double
fn identity(x):
    return x

main = identity(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    // identity(5) = 5, double -> 10, add_ten -> 20
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_decorator_no_parens() {
    // Simple decorator without parentheses - just verifies the syntax works
    // (This is essentially the same as decorator_basic but confirms no-parens syntax)
    let code = r#"
fn add_five(f):
    fn wrapper(x):
        return f(x) + 5
    return wrapper

@add_five
fn square(x):
    return x * x

main = square(4)
"#;
    let result = run_code(code, &[], "").unwrap();
    // square(4) = 16, then + 5 = 21
    assert_eq!(result.exit_code, 21);
}

// ============= Attributes =============
// Attributes are compile-time metadata that can be attached to items.
// Currently we support: #[inline], #[deprecated], #[allow(...)]

#[test]
fn interpreter_attribute_inline() {
    // #[inline] is a hint for the compiler - doesn't affect runtime behavior
    let code = r#"
#[inline]
fn add(a, b):
    return a + b

main = add(3, 4)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7);
}

#[test]
fn interpreter_attribute_deprecated() {
    // #[deprecated] marks an item as deprecated - still usable but may warn
    let code = r#"
#[deprecated]
fn old_api(x):
    return x * 2

main = old_api(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_attribute_with_value() {
    // #[deprecated = "message"] - attribute with value
    let code = r#"
#[deprecated = "use new_api instead"]
fn legacy(x):
    return x + 1

main = legacy(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

#[test]
fn interpreter_multiple_attributes() {
    // Multiple attributes on same function
    let code = r#"
#[inline]
#[deprecated]
fn double(x):
    return x * 2

main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_attribute_on_class() {
    // Attributes on class - just verify parsing, execution uses simpler pattern
    let code = r#"
#[deprecated]
class Point:
    x: int
    y: int

# Since class instantiation with __init__ has limitations, just verify parsing
# and return a constant to confirm attributes didn't break anything
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============= Result Type =============
// Result[T, E] for explicit error handling with Ok and Err variants

#[test]
fn interpreter_result_ok_unwrap() {
    // Basic Result with Ok variant - test unwrap
    let code = r#"
result = Ok(42)
main = result.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_result_is_ok() {
    // Check if result is Ok
    let code = r#"
result = Ok(10)
x = 0
if result.is_ok():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_result_is_err() {
    // Check if result is Err
    let code = r#"
result = Err("error")
x = 0
if result.is_err():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_result_unwrap_or() {
    // Unwrap with default value for Err
    let code = r#"
err_result = Err("oops")
main = err_result.unwrap_or(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

#[test]
fn interpreter_result_from_function() {
    // Function returning Result
    let code = r#"
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

r = safe_divide(20, 4)
main = r.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_result_err_handling() {
    // Function returning Err, handle with unwrap_or
    let code = r#"
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

r = safe_divide(10, 0)
main = r.unwrap_or(-1)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

// ============= ? Operator =============
// The ? operator for error propagation (early return on Err)

#[test]
fn interpreter_question_mark_operator() {
    // ? operator propagates errors
    let code = r#"
fn may_fail(x) -> Result[int, str]:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    val = may_fail(x)?  # If Err, early return with the error
    return Ok(val + 1)

result = caller(5)
main = result.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    // 5 * 2 = 10, then + 1 = 11
    assert_eq!(result.exit_code, 11);
}

#[test]
fn interpreter_question_mark_propagates_error() {
    // ? operator propagates the error to caller
    let code = r#"
fn may_fail(x) -> Result[int, str]:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    val = may_fail(x)?
    return Ok(val + 1)

result = caller(-5)  # Will return Err("negative")
main = result.unwrap_or(-99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -99);
}

#[test]
fn interpreter_question_mark_chained() {
    // Multiple ? operators in chain
    let code = r#"
fn step1(x):
    if x < 0:
        return Err("step1 failed")
    return Ok(x + 10)

fn step2(x):
    if x > 100:
        return Err("step2 failed")
    return Ok(x * 2)

fn pipeline(x):
    a = step1(x)?
    b = step2(a)?
    return Ok(b)

result = pipeline(5)
main = result.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    // 5 + 10 = 15, 15 * 2 = 30
    assert_eq!(result.exit_code, 30);
}

// ============= Match Guards (#74) =============
// Match guards allow conditional patterns: case x if condition:

#[test]
fn interpreter_match_guard_basic() {
    // Basic match guard with if condition
    let code = r#"
fn classify(x):
    match x:
        n if n < 0 =>
            return -1
        n if n == 0 =>
            return 0
        n if n > 0 =>
            return 1
    return -99

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_guard_negative() {
    let code = r#"
fn classify(x):
    match x:
        n if n < 0 =>
            return -1
        n if n == 0 =>
            return 0
        n if n > 0 =>
            return 1
    return -99

main = classify(-10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

#[test]
fn interpreter_match_guard_uses_binding() {
    // Guard can use the bound variable
    let code = r#"
fn check(pair):
    match pair:
        (a, b) if a + b > 10 =>
            return 1
        (a, b) if a + b == 10 =>
            return 0
        _ =>
            return -1
    return -99

main = check((7, 5))  # 7 + 5 = 12 > 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_guard_fallthrough() {
    // When guard fails, try next arm
    let code = r#"
fn test(x):
    match x:
        n if n > 100 =>
            return 100
        n if n > 10 =>
            return 10
        n =>
            return n
    return -99

main = test(50)  # 50 > 100? No. 50 > 10? Yes -> return 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

// ============= If Let / While Let (#75) =============
// Pattern matching in conditionals: if let pattern = expr:

#[test]
fn interpreter_if_let_some() {
    // If let with Option/Some pattern
    let code = r#"
opt = Some(42)
result = 0
if let Some(x) = opt:
    result = x
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_if_let_none_else() {
    // If let with else branch for non-matching
    let code = r#"
opt = None
result = 0
if let Some(x) = opt:
    result = x
else:
    result = -1
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

#[test]
fn interpreter_if_let_ok() {
    // If let with Result/Ok pattern
    let code = r#"
res = Ok(100)
result = 0
if let Ok(val) = res:
    result = val
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_while_let_basic() {
    // While let loop that extracts values
    let code = r#"
fn next_item(n):
    if n > 0:
        return Some(n)
    return None

counter = 3
sum = 0
while let Some(val) = next_item(counter):
    sum = sum + val
    counter = counter - 1
main = sum  # 3 + 2 + 1 = 6
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

// ============= Or Patterns (#80) =============
// Match multiple patterns with |

#[test]
fn interpreter_or_pattern_basic() {
    // Match multiple literal values
    let code = r#"
fn classify(x):
    match x:
        1 | 2 | 3 =>
            return 1  # small
        4 | 5 | 6 =>
            return 2  # medium
        _ =>
            return 3  # large

main = classify(2)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // 2 matches first group
}

#[test]
fn interpreter_or_pattern_medium() {
    let code = r#"
fn classify(x):
    match x:
        1 | 2 | 3 =>
            return 1  # small
        4 | 5 | 6 =>
            return 2  # medium
        _ =>
            return 3  # large

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // 5 matches second group
}

#[test]
fn interpreter_or_pattern_with_wildcard() {
    let code = r#"
fn check(x):
    match x:
        0 | 1 =>
            return 10
        _ =>
            return 99

main = check(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

// ============= Range Patterns (#81) =============
// Match a range of values with .. or ..=

#[test]
fn interpreter_range_pattern_exclusive() {
    // Exclusive range 0..10 (includes 0-9)
    let code = r#"
fn classify(x):
    match x:
        0..10 =>
            return 1
        10..20 =>
            return 2
        _ =>
            return 3

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_range_pattern_exclusive_boundary() {
    // Test that exclusive range doesn't include end
    let code = r#"
fn classify(x):
    match x:
        0..10 =>
            return 1
        10..20 =>
            return 2
        _ =>
            return 3

main = classify(10)  # 10 is not in 0..10, but is in 10..20
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_range_pattern_inclusive() {
    // Inclusive range 0..=10 (includes 0-10)
    let code = r#"
fn classify(x):
    match x:
        0..=5 =>
            return 1
        6..=10 =>
            return 2
        _ =>
            return 3

main = classify(5)  # 5 is in 0..=5
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// Note: Negative number patterns like -10..0 are not supported yet
// as the pattern parser doesn't handle unary minus

// ============= Hexadecimal Literals (#93) =============

#[test]
fn interpreter_hex_literal() {
    let code = r#"
x = 0xFF
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_hex_arithmetic() {
    let code = r#"
x = 0x10 + 0x20
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 48); // 16 + 32 = 48
}

// ============= Binary Literals (#94) =============

#[test]
fn interpreter_binary_literal() {
    let code = r#"
x = 0b1010
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_binary_with_underscores() {
    let code = r#"
x = 0b1111_0000
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 240);
}

// ============= Octal Literals (#95) =============

#[test]
fn interpreter_octal_literal() {
    let code = r#"
x = 0o755
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 493); // 7*64 + 5*8 + 5 = 493
}
