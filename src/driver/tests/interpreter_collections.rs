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

