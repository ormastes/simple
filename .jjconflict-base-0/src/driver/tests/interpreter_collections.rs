#![allow(unused_imports)]

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
    value = x + 1
main = value
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
    ret_value = v

main = ret_value
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
