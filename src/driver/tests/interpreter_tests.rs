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
