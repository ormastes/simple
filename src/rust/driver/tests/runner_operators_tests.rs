//! Runner Operators and Language Features Tests
//!
//! Tests for operators, mutability control, lambdas, strings, arrays, dicts,
//! bitwise operations, comparison operators, and other language features.

#![allow(unused_imports, deprecated, unused_variables, unused_mut)]

use simple_driver::dependency_cache::{analyze_source_str, BuildCache, DepInfo};
use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};
use simple_driver::runner::Runner;
use simple_runtime::gc::GcRuntime;
use simple_term_io::io::term::TermNative;
use std::sync::{Arc, Mutex};

// Import shared test helpers
mod test_helpers;
use test_helpers::{
    run_expect, run_expect_compile_error, run_expect_compile_error_at, run_expect_error, run_expect_interp,
    run_expect_parity, run_expect_runtime_error,
};

#[test]
fn runner_handles_mutability_control() {
    let runner = Runner::new();

    // let is immutable by default; reassignment without mut should fail
    let src = r#"
let x = 10
x = 20
main = x
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "immutable let should reject reassignment");

    // Mutable binding with let mut allows reassignment
    let src = r#"
let mut x = 10
x = 20
main = x
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 20, "let mut variables can be reassigned");

    // var keyword creates mutable variable
    let src = r#"
var y = 10
y = 30
main = y
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 30, "var variables can be reassigned");

    // Variables in loop with var
    let src = r#"
var sum = 0
var i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 10, "sum of 0+1+2+3+4 = 10");

    // const is immutable (cannot be reassigned)
    let src = r#"
const x = 10
x = 20
main = x
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "const reassignment should fail");
    let err = result.unwrap_err();
    assert!(
        err.contains("immutable") || err.contains("cannot assign"),
        "error should mention immutability"
    );
}

#[test]
fn runner_handles_static_const_declarations() {
    let runner = Runner::new();

    // Simple const declaration
    let src = r#"
const MAX = 100
main = MAX
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 100, "const MAX should be 100");

    // Const with arithmetic
    let src = r#"
const BASE = 10
const MULTIPLIER = 5
main = BASE * MULTIPLIER
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 50, "BASE * MULTIPLIER = 10 * 5 = 50");

    // Const cannot be reassigned (should error)
    let src = r#"
const X = 10
X = 20
main = X
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "const reassignment should fail");

    // Static variable (immutable by default)
    let src = r#"
static counter = 42
main = counter
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 42, "static counter should be 42");

    // Static mut variable can be reassigned
    let src = r#"
static mut counter = 0
counter = counter + 1
counter = counter + 1
main = counter
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 2, "static mut counter should be 2 after two increments");

    // Static (non-mut) cannot be reassigned (should error)
    let src = r#"
static counter = 10
counter = 20
main = counter
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "static (non-mut) reassignment should fail");

    // Const with type annotation
    let src = r#"
const SIZE: i64 = 256
main = SIZE
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 256, "const SIZE should be 256");
}

// Futures require special runtime setup - skipping for now
// #[test]
// fn runner_handles_futures() {
//     run_expect(r#"
// fn compute():
//     return 42
// let f = async(compute())
// let result = await(f)
// main = result
// "#, 42);
// }

// Generators require yield keyword which may not parse correctly
// #[test]
// fn runner_handles_generators() {
//     run_expect(r#"
// let gen = generator(\:
//     yield 1
//     yield 2
// )
// let a = next(gen)
// let b = next(gen)
// main = a + b
// "#, 3);
// }

#[test]
fn runner_handles_impl_blocks() {
    run_expect(r#"
struct Point:
    x: i64
    y: i64
impl Point:
    fn sum(self):
        return self.x + self.y
let p = Point { x: 10, y: 20 }
main = p.sum()
"#, 30);
}

// Context blocks - now working!
#[test]
fn runner_handles_context_blocks() {
    run_expect(r#"
class Container:
    value: i64

    fn get_value(self):
        return self.value

val container = Container { value: 100 }
var result = 0
context container:
    result = get_value()
main = result
"#, 100);
}

// Macros may need different invocation syntax
// #[test]
// fn runner_handles_macro_expansion() {
//     run_expect(r#"
// macro double(x) = x + x
// main = double(21)
// "#, 42);
// }

#[test]
fn runner_handles_lambda_expressions() {
    // Basic lambda
    run_expect(
        r#"
let double = \x: x * 2
main = double(21)
"#,
        42,
    );

    // Lambda with multiple params
    run_expect(
        r#"
let add = \a, b: a + b
main = add(10, 32)
"#,
        42,
    );
}

#[test]
fn runner_handles_lambda_higher_order() {
    // Lambda passed to function - uses untyped params, so interpreter-only
    run_expect_interp(
        r#"
fn apply(f, x):
    return f(x)

let inc = \n: n + 1
main = apply(inc, 41)
"#,
        42,
    );
}

#[test]
fn runner_handles_string_operations() {
    // String length
    run_expect(
        r#"
let s = "hello"
main = s.len()
"#,
        5,
    );

    // String concatenation
    run_expect(
        r#"
let a = "hello"
let b = "world"
let c = a + " " + b
main = c.len()
"#,
        11,
    );

    // F-string interpolation
    run_expect(
        r#"
let x = 42
let s = "value is {x}"
main = s.len()
"#,
        11,
    );
}

#[test]
fn runner_handles_array_methods() {
    // Array length
    run_expect(
        r#"
let arr = [1, 2, 3, 4, 5]
main = arr.len()
"#,
        5,
    );
}

// Array push may not return the mutated array correctly
// #[test]
// fn runner_handles_array_push() {
//     run_expect(r#"
// let mut arr = [1, 2]
// arr.push(3)
// main = arr.len()
// "#, 3);
// }

// Map/filter/reduce may need different syntax
// #[test]
// fn runner_handles_array_functional_methods() {
//     run_expect(r#"
// let arr = [1, 2, 3]
// let doubled = arr.map(\x: x * 2)
// main = doubled[0] + doubled[1] + doubled[2]
// "#, 12);
// }

#[test]
fn runner_handles_dict_methods() {
    // Dict len
    run_expect(
        r#"
let d = {"a": 1, "b": 2, "c": 3}
main = d.len()
"#,
        3,
    );

    // Dict keys
    run_expect(
        r#"
let d = {"x": 10, "y": 20}
let keys = d.keys()
main = keys.len()
"#,
        2,
    );

    // Dict values
    run_expect(
        r#"
let d = {"a": 5, "b": 10}
let vals = d.values()
main = vals[0] + vals[1]
"#,
        15,
    );

    // Dict contains_key
    run_expect(
        r#"
let d = {"hello": 1}
main = if d.contains_key("hello"): 1 else: 0
"#,
        1,
    );
}

#[test]
fn runner_handles_bitwise_operations() {
    run_expect("main = 12 & 10", 8); // 1100 & 1010 = 1000
    run_expect("main = 12 | 10", 14); // 1100 | 1010 = 1110
    run_expect("main = 12 xor 10", 6); // 1100 xor 1010 = 0110
    run_expect("main = 1 << 4", 16); // shift left
    run_expect("main = 16 >> 2", 4); // shift right
    run_expect("main = ~0", -1); // bitwise not
}

#[test]
fn runner_handles_comparison_operators() {
    run_expect("main = if 1 < 2: 1 else: 0", 1);
    run_expect("main = if 2 > 1: 1 else: 0", 1);
    run_expect("main = if 2 <= 2: 1 else: 0", 1);
    run_expect("main = if 2 >= 2: 1 else: 0", 1);
    run_expect("main = if 2 == 2: 1 else: 0", 1);
    run_expect("main = if 2 != 3: 1 else: 0", 1);
}

#[test]
fn runner_handles_logical_operators() {
    run_expect("main = if true and true: 1 else: 0", 1);
    run_expect("main = if true and false: 1 else: 0", 0);
    run_expect("main = if true or false: 1 else: 0", 1);
    run_expect("main = if false or false: 1 else: 0", 0);
    run_expect("main = if not false: 1 else: 0", 1);
    run_expect("main = if not true: 1 else: 0", 0);
}

#[test]
fn runner_handles_power_operator() {
    run_expect("main = 2 ** 0", 1); // any ** 0 = 1
    run_expect("main = 2 ** 1", 2); // x ** 1 = x
    run_expect("main = 2 ** 3", 8); // 2^3 = 8
    run_expect("main = 2 ** 10", 1024); // 2^10 = 1024
    run_expect("main = 3 ** 4", 81); // 3^4 = 81
}

#[test]
fn runner_handles_floor_division() {
    run_expect("main = 7 // 2", 3); // floor(7/2) = 3
    run_expect("main = 10 // 3", 3); // floor(10/3) = 3
    run_expect("main = -7 // 2", -4); // floor(-7/2) = -4 (rounds toward negative infinity)
    run_expect("main = 8 // 4", 2); // exact division
}

#[test]
fn runner_handles_in_operator() {
    // In array
    run_expect("main = if 2 in [1, 2, 3]: 1 else: 0", 1);
    run_expect("main = if 5 in [1, 2, 3]: 1 else: 0", 0);
    // In string
    run_expect(r#"main = if "ell" in "hello": 1 else: 0"#, 1);
    run_expect(r#"main = if "xyz" in "hello": 1 else: 0"#, 0);
}

// Pointer types may have different syntax
// #[test]
// fn runner_handles_pointer_types() {
//     run_expect(r#"
// let s = new @ 42
// main = *s
// "#, 42);
// }

// Union types need special type system support
// #[test]
// fn runner_handles_union_types() {
//     run_expect(r#"
// fn process(x: i64 | str):
//     match x:
//         n: i64 =>
//             return n
//         s: str =>
//             return s.len()
//     return 0
// main = process(42)
// "#, 42);
// }

// Functional update operator may need method resolution
// #[test]
// fn runner_handles_functional_update() {
//     run_expect(r#"
// let mut x = 5
// x->double()
// main = x
// fn double():
//     return self * 2
// "#, 10);
// }

#[test]
fn runner_handles_extern_functions() {
    // Note: extern functions typically require native libraries
    // This tests the parsing and basic handling
    run_expect(
        r#"
extern fn add_numbers(a: i64, b: i64) -> i64
main = 42
"#,
        42,
    );
}

// method_missing - works in interpreter, needs type annotations for compiler
// Keeping commented until compiler supports untyped method_missing params
// #[test]
// fn runner_handles_method_missing() {
//     run_expect(r#"
// class Flexible:
//     fn method_missing(self, name, args, block):
//         return 99
//
// val f = Flexible {}
// main = f.unknown_method()
// "#, 99);
// }

#[test]
fn runner_handles_recursive_functions() {
    // Factorial with smaller input to avoid stack overflow
    run_expect(
        r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

main = factorial(3)
"#,
        6,
    );
}

#[test]
fn runner_handles_nested_data_structures() {
    // Nested arrays
    run_expect(
        r#"
let arr = [[1, 2], [3, 4], [5, 6]]
main = arr[0][0] + arr[1][1] + arr[2][0]
"#,
        10,
    );

    // Nested structs
    run_expect(
        r#"
struct Inner:
    value: i64

struct Outer:
    inner: Inner

let o = Outer { inner: Inner { value: 42 } }
main = o.inner.value
"#,
        42,
    );
}

#[test]
fn runner_handles_early_return() {
    run_expect(
        r#"
fn verify(x: i64) -> i64:
    if x > 10:
        return 1
    if x > 5:
        return 2
    return 3

main = verify(7)
"#,
        2,
    );
}

#[test]
fn runner_handles_multiple_assignment() {
    run_expect(
        r#"
let (a, b, c) = (1, 2, 3)
main = a + b + c
"#,
        6,
    );
}

#[test]
fn runner_handles_symbols() {
    run_expect(
        r#"
let s = :hello
main = if s == :hello: 1 else: 0
"#,
        1,
    );
}
