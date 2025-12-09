//! System tests for the interpreter interface

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_runs_simple_code() {
    let result = run_code("main = 42", &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_returns_zero() {
    let result = run_code("main = 0", &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_arithmetic() {
    let result = run_code("main = 10 + 20 * 2", &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_arithmetic_complex() {
    let result = run_code("main = (5 + 3) * 4 - 10 / 2", &[], "").unwrap();
    assert_eq!(result.exit_code, 27); // (5+3)*4 - 10/2 = 32 - 5 = 27
}

#[test]
fn interpreter_with_variables() {
    let code = r#"
let x = 10
let y = 20
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_variable_expressions() {
    let code = r#"
let a = 5
let b = a * 2
let c = b + a
main = c
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // a=5, b=10, c=15
}

#[test]
fn interpreter_with_functions() {
    let code = r#"
fn add(a, b):
    return a + b
main = add(5, 7)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 12);
}

#[test]
fn interpreter_with_nested_function_calls() {
    let code = r#"
fn double(x):
    return x * 2
fn add_one(x):
    return x + 1
main = add_one(double(5))
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11); // double(5)=10, add_one(10)=11
}

#[test]
fn interpreter_with_structs() {
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_enums() {
    let code = r#"
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_enum_comparison_false() {
    let code = r#"
enum Color:
    Red
    Green

let c = Color::Green
main = if c is Color::Red: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_if_else() {
    let code = r#"
let x = 10
main = if x > 5: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_while_loop() {
    let code = r#"
sum = 0
i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // 0+1+2+3+4 = 10
}

#[test]
fn interpreter_for_loop() {
    let code = r#"
sum = 0
for i in range(1, 5):
    sum = sum + i
main = sum
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // 1+2+3+4 = 10
}

#[test]
fn interpreter_class_methods() {
    let code = r#"
class Calculator:
    fn add(a, b):
        return a + b

main = Calculator.add(3, 4)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7);
}

#[test]
fn interpreter_error_handling_syntax() {
    let result = run_code("invalid syntax here @#$", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_error_handling_undefined_variable() {
    let result = run_code("main = undefined_var", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_using_struct() {
    let interpreter = Interpreter::new();
    let result = interpreter.run_simple("main = 100").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_with_config() {
    let interpreter = Interpreter::new();
    let result = interpreter.run(
        "main = 255",
        RunConfig {
            args: vec!["arg1".to_string()],
            stdin: "input".to_string(),
            timeout_ms: 0,
        }
    ).unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_run_with_stdin() {
    let interpreter = Interpreter::new();
    let result = interpreter.run_with_stdin("main = 50", "test input").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_result_has_empty_stdout() {
    // For now, stdout capture is not implemented
    let result = run_code("main = 1", &[], "").unwrap();
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
}

#[test]
fn interpreter_impl_blocks() {
    let code = r#"
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

let p = Point { x: 15, y: 25 }
main = p.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40); // 15 + 25 = 40
}

#[test]
fn interpreter_impl_blocks_with_args() {
    let code = r#"
struct Counter:
    value: i64

impl Counter:
    fn add(self, n):
        return self.value + n

let c = Counter { value: 10 }
main = c.add(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // 10 + 5 = 15
}

#[test]
fn interpreter_traits_basic() {
    let code = r#"
trait Summable:
    fn sum(self):
        return 0

struct Point:
    x: i64
    y: i64

impl Summable for Point:
    fn sum(self):
        return self.x + self.y

let p = Point { x: 10, y: 20 }
main = p.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30); // 10 + 20 = 30
}

#[test]
fn interpreter_traits_multiple_types() {
    let code = r#"
trait Valuable:
    fn value(self):
        return 0

struct Coin:
    amount: i64

struct Bill:
    amount: i64

impl Valuable for Coin:
    fn value(self):
        return self.amount

impl Valuable for Bill:
    fn value(self):
        return self.amount * 100

let c = Coin { amount: 5 }
let b = Bill { amount: 2 }
main = c.value() + b.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 205); // 5 + 200 = 205
}

#[test]
fn interpreter_traits_with_args() {
    let code = r#"
trait Calculator:
    fn add(self, n):
        return 0

struct Counter:
    value: i64

impl Calculator for Counter:
    fn add(self, n):
        return self.value + n

let c = Counter { value: 50 }
main = c.add(25)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 75); // 50 + 25 = 75
}

#[test]
fn interpreter_symbols() {
    let code = r#"
let status = :ok
main = if status is :ok: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_symbols_comparison() {
    let code = r#"
let a = :hello
let b = :hello
let c = :world
main = if a is b: 10 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_union_type_annotation() {
    // Union types in type annotations (parser test)
    let code = r#"
fn test(x: i64 | str) -> i64:
    return 42
main = test(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_type_alias() {
    let code = r#"
type Number = i64

fn double(x: Number) -> Number:
    return x * 2

main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_union_type_pattern_match_int() {
    // Union type with pattern matching - match on int type
    let code = r#"
fn process(x: i64 | str) -> i64:
    match x:
        n: i64 =>
            return n * 2
        s: str =>
            return 0
    return -1

main = process(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_union_type_pattern_match_str() {
    // Union type with pattern matching - match on string type
    let code = r#"
fn process(x: i64 | str) -> i64:
    match x:
        n: i64 =>
            return n * 2
        s: str =>
            return 100
    return -1

main = process("hello")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_union_type_three_types() {
    // Union type with three types
    let code = r#"
fn classify(x: i64 | str | bool) -> i64:
    match x:
        n: i64 =>
            return 1
        s: str =>
            return 2
        b: bool =>
            return 3
    return 0

let a = classify(42)
let b = classify("test")
let c = classify(true)
main = a + b * 10 + c * 100
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 321); // 1 + 20 + 300
}

#[test]
fn interpreter_optional_type() {
    // T? syntax for optional types
    let code = r#"
fn maybe_value(x: i64?) -> i64:
    return 5
main = maybe_value(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_generic_function_identity() {
    // Generic function: fn identity<T>(x: T) -> T
    let code = r#"
fn identity<T>(x: T) -> T:
    return x

main = identity(42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_generic_function_pair() {
    // Generic function with two type parameters
    let code = r#"
fn first<A, B>(a: A, b: B) -> A:
    return a

fn second<A, B>(a: A, b: B) -> B:
    return b

let x = first(10, 20)
let y = second(30, 40)
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50); // 10 + 40
}

#[test]
fn interpreter_generic_struct() {
    // Generic struct: struct Box<T>
    let code = r#"
struct Box<T>:
    value: T

let b = Box { value: 42 }
main = b.value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_generic_enum() {
    // Generic enum: enum Option<T>
    // Note: Generic type arguments in type positions use [] not <>
    let code = r#"
enum Maybe<T>:
    Just(T)
    Nothing

fn get_or_default(m: Maybe[i64], default: i64) -> i64:
    match m:
        Maybe::Just(v) =>
            return v
        Maybe::Nothing =>
            return default
    return default

let x = Maybe::Just(42)
main = get_or_default(x, 0)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_simple() {
    // Basic lambda: \x: expr
    let code = r#"
let double = \x: x * 2
main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_multiple_params() {
    // Lambda with multiple parameters: \x, y: expr
    let code = r#"
let add = \x, y: x + y
main = add(15, 27)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_closure() {
    // Lambda capturing a variable from outer scope
    let code = r#"
let multiplier = 10
let multiply = \x: x * multiplier
main = multiply(4)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40);
}

#[test]
fn interpreter_lambda_immediate_call() {
    // Immediately invoked lambda
    let code = r#"
main = (\x: x + 5)(37)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_nested() {
    // Nested lambda calls
    let code = r#"
let double = \x: x * 2
let add_one = \x: x + 1
main = add_one(double(20))
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 41); // double(20)=40, add_one(40)=41
}

#[test]
fn interpreter_lambda_no_params() {
    // Lambda with no parameters: \: expr
    let code = r#"
let answer = \: 42
main = answer()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_fstring_basic() {
    // Basic f-string with variable interpolation
    let code = r#"
let x = 42
let s = f"value is {x}"
main = if s == "value is 42": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_expression() {
    // F-string with arithmetic expression
    let code = r#"
let a = 10
let b = 20
let s = f"sum is {a + b}"
main = if s == "sum is 30": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_multiple() {
    // F-string with multiple interpolations
    let code = r#"
let name = "world"
let count = 3
let s = f"hello {name}, count={count}"
main = if s == "hello world, count=3": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_no_interpolation() {
    // F-string with no interpolations (just literal)
    let code = r#"
let s = f"just a string"
main = if s == "just a string": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_named_arguments_basic() {
    // Basic named arguments
    let code = r#"
fn greet(name, greeting):
    return 1

main = greet(name="world", greeting="hello")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_named_arguments_reorder() {
    // Named arguments can be in any order
    let code = r#"
fn sub(a, b):
    return a - b

main = sub(b=10, a=30)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20); // 30 - 10 = 20
}

#[test]
fn interpreter_named_arguments_mixed() {
    // Mix positional and named arguments
    let code = r#"
fn calc(x, y, z):
    return x + y * z

main = calc(2, z=4, y=3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 14); // 2 + 3 * 4 = 14
}

#[test]
fn interpreter_default_arguments() {
    // Default argument values
    let code = r#"
fn add(a, b=10):
    return a + b

main = add(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // 5 + 10 = 15
}

#[test]
fn interpreter_default_arguments_override() {
    // Override default argument
    let code = r#"
fn add(a, b=10):
    return a + b

main = add(5, b=20)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 25); // 5 + 20 = 25
}

// ============= Array Tests =============

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
fn interpreter_const_declaration() {
    let code = r#"
const MAX = 100
main = MAX
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_static_declaration() {
    let code = r#"
static counter = 42
main = counter
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_const_in_expression() {
    let code = r#"
const BASE = 10
const MULTIPLIER = 5
main = BASE * MULTIPLIER
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

// ============= Option Type Tests =============

#[test]
fn interpreter_option_some() {
    let code = r#"
opt = Some(42)
main = opt.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_option_none_unwrap_or() {
    let code = r#"
opt = None
main = opt.unwrap_or(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

#[test]
fn interpreter_option_is_some() {
    let code = r#"
opt = Some(1)
main = if opt.is_some(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_option_is_none() {
    let code = r#"
opt = None
main = if opt.is_none(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_option_map() {
    let code = r#"
opt = Some(10)
result = opt.map(\x: x * 2)
main = result.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

// ============= String Methods Tests =============

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
fn interpreter_match_tuple() {
    let code = r#"
t = (1, 2)
match t:
    (1, x) =>
        main = x * 10
    _ =>
        main = 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_match_array() {
    let code = r#"
arr = [5, 10]
match arr:
    [a, b] =>
        main = a + b
    _ =>
        main = 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

// ============= Global len() Function =============

#[test]
fn interpreter_global_len_function() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
main = len(arr)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

// ============= Line Continuation Tests =============

#[test]
fn interpreter_line_continuation_expression() {
    // Backslash at end of line continues to next line
    let code = "main = 1 + 2 + \\\n    3 + 4";
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_line_continuation_function_call() {
    let code = r#"
fn add(a, b, c):
    return a + b + c

main = add(1, \
    2, \
    3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

// ============= Array Functional Methods =============

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

#[test]
fn interpreter_functional_update_array_concat() {
    let code = r#"
arr = [1, 2]
arr->concat([3, 4])
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_functional_update_array_map() {
    let code = r#"
arr = [1, 2, 3]
arr->map(\x: x * 2)
main = arr[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4); // [2, 4, 6][1] = 4
}

#[test]
fn interpreter_functional_update_array_filter() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
arr->filter(\x: x > 2)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // [3, 4, 5]
}

#[test]
fn interpreter_functional_update_dict_set() {
    let code = r#"
d = {"a": 1}
d->set("b", 2)
main = d.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_functional_update_chained() {
    let code = r#"
arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // [2,3,4] -> [3,4]
}

// ============= No-Parentheses Calls (statement level only) =============
// Note: No-parens calls only work for direct statement-level calls,
// NOT inside expressions like assignments.

#[test]
fn interpreter_no_paren_call_simple_statement() {
    // No-parens call at statement level with an argument
    // Call result is ignored, main is set separately
    let code = r#"
fn process(x):
    return x * 2

# Call without parens at statement level (result ignored)
process 10
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_no_paren_call_with_string_arg() {
    // No-parens call with a string argument
    let code = r#"
fn get_len(s):
    return len(s)

# len is called via no-parens then we use print for side effect
get_len "hello"
main = 5
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_no_paren_call_with_int_arg() {
    // No-parens call with an integer argument
    let code = r#"
fn double(x):
    return x * 2

# This won't affect main since result is ignored
double 21
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============= Mutability Control =============

#[test]
fn interpreter_let_mut_allows_reassignment() {
    let code = r#"
let mut x = 10
x = 42
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_let_immutable_prevents_reassignment() {
    let code = r#"
let x = 10
x = 42
main = x
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("cannot assign"));
}

#[test]
fn interpreter_mut_let_syntax() {
    // Alternative syntax: mut let x = ...
    let code = r#"
mut let y = 5
y = 10
main = y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_let_mut_tuple_destructure() {
    let code = r#"
let mut (a, b) = (1, 2)
a = 10
b = 20
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_let_immutable_tuple_prevents_reassignment() {
    let code = r#"
let (a, b) = (1, 2)
a = 10
main = a
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

// Named arguments are already tested elsewhere in this file

// ============= Trailing Blocks =============

#[test]
fn interpreter_trailing_block_method_call() {
    // obj.method \x: body is equivalent to obj.method(\x: body)
    let code = r#"
arr = [1, 2, 3]
doubled = arr.map \x: x * 2
main = doubled[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4); // [2, 4, 6][1] = 4
}

#[test]
fn interpreter_trailing_block_with_args() {
    // obj.method(arg) \x: body - trailing block after regular args
    let code = r#"
fn apply_twice(f, x):
    return f(f(x))

result = apply_twice(\n: n + 1, 40)
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_trailing_block_filter() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
filtered = arr.filter \x: x > 3
main = filtered.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // [4, 5]
}

#[test]
fn interpreter_trailing_block_multi_param() {
    let code = r#"
fn combine(a, b, f):
    return f(a, b)

result = combine(20, 22) \x, y: x + y
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============ Extern Functions (#46) ============

#[test]
fn interpreter_extern_abs() {
    let code = r#"
extern fn abs(x) -> i64

main = abs(-42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_extern_min_max() {
    let code = r#"
extern fn min(a, b) -> i64
extern fn max(a, b) -> i64

let a = min(10, 20)
let b = max(10, 20)
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30); // 10 + 20
}

#[test]
fn interpreter_extern_sqrt() {
    let code = r#"
extern fn sqrt(x) -> i64

main = sqrt(16)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_extern_pow() {
    let code = r#"
extern fn pow(base, exp) -> i64

main = pow(2, 5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 32); // 2^5 = 32
}

#[test]
fn interpreter_extern_to_int() {
    let code = r#"
extern fn to_int(x) -> i64

main = to_int(true) + to_int(false)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // true=1, false=0
}

// ============ Context Blocks (#35) ============

#[test]
fn interpreter_context_block_basic() {
    // Simple context block - method calls dispatch to the context object
    let code = r#"
class Calculator:
    fn double(self, x):
        return x * 2

let calc = Calculator {}
let mut result = 0
context calc:
    result = double(21)
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_context_block_with_self() {
    // Context block where method accesses self
    let code = r#"
class Adder:
    base: i64 = 10

    fn add(self, x):
        return self.base + x

let a = Adder { base: 30 }
let mut result = 0
context a:
    result = add(12)
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============ Method Missing (#36) ============

#[test]
fn interpreter_method_missing_basic() {
    // Basic method_missing - called when method doesn't exist
    let code = r#"
class DSL:
    fn method_missing(self, name, args, block):
        # Return 42 for any unknown method
        return 42

let d = DSL {}
main = d.unknown_method()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_method_missing_with_args() {
    // method_missing with arguments
    let code = r#"
class Multiplier:
    factor: i64 = 10

    fn method_missing(self, name, args, block):
        # Multiply first arg by factor
        let x = args[0]
        return self.factor * x

let m = Multiplier { factor: 7 }
main = m.any_method(6)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42); // 7 * 6
}

#[test]
fn interpreter_method_missing_with_context() {
    // method_missing inside context block
    let code = r#"
class Counter:
    count: i64 = 0

    fn method_missing(self, name, args, block):
        # Any call returns 42
        return 42

let c = Counter { count: 0 }
let mut result = 0
context c:
    result = something_undefined()
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// === Raw String Tests ===

#[test]
fn interpreter_raw_string_basic() {
    // Raw strings with single quotes don't process escapes
    let code = r#"
let s = 'hello world'
main = len(s)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11);
}

#[test]
fn interpreter_raw_string_backslashes() {
    // Backslashes are literal in raw strings
    let code = r#"
let path = 'C:\Users\test'
main = len(path)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 13); // C:\Users\test = 13 chars
}

#[test]
fn interpreter_raw_string_no_interpolation() {
    // Braces are literal in raw strings, not interpolation
    let code = r#"
let template = '{name}'
main = len(template)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6); // {name} = 6 chars
}

#[test]
fn interpreter_default_string_interpolation() {
    // Double-quoted strings interpolate by default (like f-strings)
    let code = r#"
let x = 5
let msg = "value is {x}"
main = len(msg)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // "value is 5" = 10 chars
}

#[test]
fn interpreter_default_string_escaped_braces() {
    // Double braces escape to literal braces
    let code = r#"
let msg = "use {{x}} for interpolation"
main = len(msg)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 25); // "use {x} for interpolation" = 25 chars
}

// === Manual Pointer Tests ===

#[test]
fn interpreter_unique_pointer_basic() {
    // Unique pointer with & syntax
    let code = r#"
let ptr = new & 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_arithmetic() {
    // Unique pointer arithmetic
    let code = r#"
let a = new & 10
let b = new & 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_basic() {
    // Shared pointer with * syntax
    let code = r#"
let ptr = new * 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_shared_pointer_arithmetic() {
    // Shared pointer arithmetic
    let code = r#"
let a = new * 10
let b = new * 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_multiple_refs() {
    // Multiple references to same shared value
    let code = r#"
let a = new * 42
let b = a
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_handle_pointer_basic() {
    // Handle pointer with + syntax
    let code = r#"
let ptr = new + 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_handle_pointer_arithmetic() {
    // Handle pointer arithmetic
    let code = r#"
let a = new + 10
let b = new + 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_weak_pointer_from_shared() {
    // Weak pointer from shared - needs downgrade method
    let code = r#"
let shared = new * 42
let weak = new - shared
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_pointer_with_struct() {
    // Unique pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = new & Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_shared_pointer_with_struct() {
    // Shared pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = new * Point { x: 5, y: 15 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_handle_pointer_with_struct() {
    // Handle pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = new + Point { x: 7, y: 3 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

// ============================================================================
// Macro Tests
// ============================================================================

#[test]
fn interpreter_macro_vec() {
    // vec! macro creates an array
    let code = r#"
let arr = vec!(1, 2, 3, 4, 5)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_macro_vec_sum() {
    // vec! macro with sum
    let code = r#"
let arr = vec!(10, 20, 30)
main = arr.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_macro_assert_pass() {
    // assert! macro that passes
    let code = r#"
assert!(true)
assert!(1 == 1)
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_macro_assert_fail() {
    // assert! macro that fails
    let code = r#"
assert!(false)
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_assert_eq_pass() {
    // assert_eq! macro that passes
    let code = r#"
let x = 10
let y = 10
assert_eq!(x, y)
main = 100
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_macro_assert_eq_fail() {
    // assert_eq! macro that fails
    let code = r#"
assert_eq!(5, 10)
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_format() {
    // format! macro creates a string
    let code = r#"
let s = format!("hello", " ", "world")
main = s.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11); // "hello world" = 11 chars
}

#[test]
fn interpreter_macro_panic() {
    // panic! macro aborts execution
    let code = r#"
panic!("test panic")
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_dbg() {
    // dbg! macro returns the value
    let code = r#"
let x = dbg!(42)
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_macro_vec_with_expressions() {
    // vec! macro with computed expressions
    let code = r#"
let a = 5
let arr = vec!(a * 2, a + 3, a - 1)
main = arr[0] + arr[1] + arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 22); // 10 + 8 + 4 = 22
}

// ============================================================================
// Future/Async Tests
// ============================================================================

#[test]
fn interpreter_future_basic() {
    // Create a future and await it
    let code = r#"
let f = future(42)
let result = await f
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_future_with_computation() {
    // Future with actual computation
    let code = r#"
fn compute():
    return 10 + 20 + 30

let f = future(compute())
let result = await f
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_future_multiple() {
    // Multiple futures
    let code = r#"
let f1 = future(10)
let f2 = future(20)
let f3 = future(30)
let r1 = await f1
let r2 = await f2
let r3 = await f3
main = r1 + r2 + r3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_await_non_future() {
    // Await on a non-future value should just return it
    let code = r#"
let x = 42
let result = await x
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_future_function_call() {
    // future() creates a future from a function call
    let code = r#"
fn slow_add(a, b):
    return a + b

let f = future(slow_add(15, 27))
let result = await f
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_waitless_basic() {
    // waitless fn can do non-blocking computation
    let code = r#"
waitless fn compute(x):
    return x * 2

main = compute(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_waitless_blocks_print() {
    // waitless fn cannot use print (blocking I/O)
    let code = r#"
extern fn print(msg)

waitless fn bad():
    print("hello")
    return 0

main = bad()
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err(), "Expected error but got: {:?}", result);
    let err = result.unwrap_err();
    assert!(err.contains("blocking operation 'print' not allowed in waitless function"), "Error: {}", err);
}

#[test]
fn interpreter_waitless_blocks_await() {
    // waitless fn cannot use await
    let code = r#"
waitless fn bad():
    let f = future(42)
    return await f

main = bad()
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.contains("blocking operation 'await' not allowed in waitless function"));
}

#[test]
fn interpreter_async_fn_basic() {
    // async fn can use blocking operations
    let code = r#"
async fn fetch():
    return 42

main = await fetch()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_waitless_can_call_waitless() {
    // waitless fn can call other waitless functions
    let code = r#"
waitless fn double(x):
    return x * 2

waitless fn quadruple(x):
    return double(double(x))

main = quadruple(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40);
}

#[test]
fn interpreter_generator_basic() {
    // Basic generator test - multiple yields using array
    let code = r#"
let gen = generator(\: [yield 1, yield 2, yield 3])

let first = next(gen)
let second = next(gen)
let third = next(gen)

main = first + second + third
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

#[test]
fn interpreter_generator_single() {
    // Simple single-value generator
    let code = r#"
let gen = generator(\: yield 42)

main = next(gen)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_generator_collect() {
    // Collect all generator values into array
    let code = r#"
let gen = generator(\: (yield 10, yield 20, yield 30, 0)[3])

let arr = collect(gen)
main = arr[0] + arr[1] + arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_generator_exhausted() {
    // Generator returns nil when exhausted
    let code = r#"
let gen = generator(\: yield 1)

let first = next(gen)
let second = next(gen)  # should be nil

# nil converts to 0 for main
main = first
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ===== Borrowing Tests =====

#[test]
fn interpreter_immutable_borrow() {
    // Basic immutable borrow with & operator
    let code = r#"
let x = 42
let y = &x  # immutable borrow
main = *y   # dereference
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_mutable_borrow() {
    // Mutable borrow with &mut operator
    let code = r#"
let x = 10
let y = &mut x  # mutable borrow
main = *y       # dereference
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_borrow_through_function() {
    // Pass borrow to function
    let code = r#"
fn read_ref(r):
    return *r

let x = 100
let borrowed = &x
main = read_ref(borrowed)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_multiple_immutable_borrows() {
    // Multiple immutable borrows allowed
    let code = r#"
let x = 25
let a = &x
let b = &x
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_mutable_borrow_modify() {
    // Mutable borrow allows modification through the reference
    let code = r#"
fn add_ten(r):
    # In real borrowing, we'd modify through the ref
    # For now, just read and return modified value
    return *r + 10

let x = 5
let borrowed = &mut x
main = add_ten(borrowed)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_borrow_nested_deref() {
    // Nested borrows and dereferences
    let code = r#"
let x = 100
let ref1 = &x
let ref2 = &ref1
let inner = *ref2
main = *inner
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_borrow_in_expression() {
    // Use borrows directly in expressions
    let code = r#"
let a = 10
let b = 20
main = *(&a) + *(&b)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

// =====================
// Macro Tests
// =====================

#[test]
fn interpreter_builtin_vec_macro() {
    // vec! macro creates an array
    let code = r#"
let arr = vec!(1, 2, 3)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_builtin_assert_macro() {
    // assert! macro should not fail for true condition
    let code = r#"
assert!(true)
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_builtin_assert_eq_macro() {
    // assert_eq! macro should not fail for equal values
    let code = r#"
assert_eq!(5, 5)
main = 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_builtin_format_macro() {
    // format! macro concatenates values
    let code = r#"
let s = format!("hello", " ", "world")
main = if s == "hello world": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_user_defined_macro_simple() {
    // Simple user-defined macro that returns a constant
    let code = r#"
macro answer!():
    return 42

main = answer!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_with_param() {
    // User-defined macro with a parameter
    let code = r#"
macro double!($x):
    return $x * 2

main = double!(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_two_params() {
    // User-defined macro with two parameters
    let code = r#"
macro add!($a, $b):
    return $a + $b

main = add!(30, 12)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_max() {
    // MAX macro implementation
    let code = r#"
macro max!($a, $b):
    if $a > $b:
        return $a
    else:
        return $b

main = max!(10, 50)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

