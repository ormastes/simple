#![allow(unused_imports)]

//! Interpreter tests - oop

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

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
fn interpreter_context_block_basic() {
    // Simple context block - method calls dispatch to the context object
    let code = r#"
class Calculator:
    fn double(self, x):
        return x * 2

let calc = Calculator {}
let mut res = 0
context calc:
    res = double(21)
main = res
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
let mut res = 0
context a:
    res = add(12)
main = res
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
let mut res = 0
context c:
    res = something_undefined()
main = res
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// === Raw String Tests ===

// ============ Auto-Forwarding Properties (#82) ============

#[test]
fn interpreter_auto_property_getter() {
    // get_ method auto-creates backing _field
    let code = r#"
class Person:
    fn get_name(self) -> str:
        return self._name

let p = Person { _name: "Alice" }
main = if p.get_name() == "Alice": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_auto_property_setter() {
    // set_ method returns modified self for chaining/update
    let code = r#"
class Counter:
    fn get_value(self) -> i64:
        return self._value

    fn set_value(self, v: i64) -> Counter:
        return Counter { _value: v }

let c = Counter { _value: 10 }
let c2 = c.set_value(42)
main = c2.get_value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_auto_property_is() {
    // is_ method auto-creates backing _field (bool type)
    let code = r#"
class Item:
    fn is_active(self) -> bool:
        return self._active

let item = Item { _active: true }
main = if item.is_active(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_auto_property_combined() {
    // Combined getter and setter with functional update pattern
    let code = r#"
class Box:
    fn get_content(self) -> i64:
        return self._content

    fn set_content(self, v: i64) -> Box:
        return Box { _content: v }

let b = Box { _content: 0 }
let b2 = b.set_content(100)
main = b2.get_content()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}
