//! Feature tests: Basic types, variables, operators, control flow, functions
//! Features #1-42: Core language features

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// Feature #1-10: Basic Types, Variables, Operators, Control Flow, Functions
// =============================================================================

/// Test Feature #1: Basic Types - integers
#[test]
fn test_feature_basic_types_integers() {
    let runner = Runner::new_no_gc();
    // i32 operations
    let result = runner
        .run_source("main = 100 + 200")
        .expect("basic int add");
    assert_eq!(result, 300);

    let result = runner
        .run_source("main = 1000 - 750")
        .expect("basic int sub");
    assert_eq!(result, 250);
}

/// Test Feature #2: Variables and let bindings
#[test]
fn test_feature_variables_let_bindings() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
let x = 10
let y = 20
main = x + y
"#,
        )
        .expect("let bindings");
    assert_eq!(result, 30);
}

/// Test Feature #4: Operators - arithmetic
#[test]
fn test_feature_operators_arithmetic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source("main = 10 + 5 * 3 - 2")
        .expect("precedence");
    assert_eq!(result, 23); // 10 + 15 - 2
}

/// Test Feature #4: Operators - comparison
#[test]
fn test_feature_operators_comparison() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 5
main = if x > 3: 1 else: 0
"#,
        )
        .expect("comparison");
    assert_eq!(result, 1);
}

/// Test Feature #4: Operators - logical
#[test]
fn test_feature_operators_logical() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = true
b = false
main = if a and not b: 1 else: 0
"#,
        )
        .expect("logical ops");
    assert_eq!(result, 1);
}

/// Test Feature #4: Operators - bitwise
#[test]
fn test_feature_operators_bitwise() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source("main = (0xFF & 0x0F) | 0x10")
        .expect("bitwise");
    assert_eq!(result, 0x1F);
}

/// Test Feature #5: Control Flow - if/else/elif (inline expression form)
#[test]
fn test_feature_control_flow_if_else() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 15
main = if x < 10: 1 elif x < 20: 2 else: 3
"#,
        )
        .expect("if/elif/else");
    assert_eq!(result, 2);
}

/// Test Feature #6: Loops - for loop
#[test]
fn test_feature_loops_for() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
sum = 0
for i in [1, 2, 3, 4, 5]:
    sum = sum + i
main = sum
"#,
        )
        .expect("for loop");
    assert_eq!(result, 15);
}

/// Test Feature #6: Loops - while loop
#[test]
fn test_feature_loops_while() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
i = 0
sum = 0
while i < 5:
    i = i + 1
    sum = sum + i
main = sum
"#,
        )
        .expect("while loop");
    assert_eq!(result, 15);
}

/// Test Feature #6: Loops - break
#[test]
fn test_feature_loops_break() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
i = 0
while true:
    i = i + 1
    if i >= 5:
        break
main = i
"#,
        )
        .expect("break");
    assert_eq!(result, 5);
}

/// Test Feature #6: Loops - continue
#[test]
fn test_feature_loops_continue() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
sum = 0
for i in [1, 2, 3, 4, 5]:
    if i == 3:
        continue
    sum = sum + i
main = sum
"#,
        )
        .expect("continue");
    assert_eq!(result, 12); // 1+2+4+5
}

/// Test Feature #7: Functions - basic
#[test]
fn test_feature_functions_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn add(a, b):
    return a + b

main = add(10, 20)
"#,
        )
        .expect("function");
    assert_eq!(result, 30);
}

/// Test Feature #7: Functions - recursion
#[test]
fn test_feature_functions_recursion() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)

main = factorial(5)
"#,
        )
        .expect("recursion");
    assert_eq!(result, 120);
}

// =============================================================================
// Feature #9-10: Structs and Classes
// =============================================================================

/// Test Feature #9: Structs - basic definition and use
#[test]
fn test_feature_structs_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
struct Point:
    x: int
    y: int

p = Point(10, 20)
main = p.x + p.y
"#,
        )
        .expect("struct basic");
    assert_eq!(result, 30);
}

/// Test Feature #10: Classes - basic definition
#[test]
fn test_feature_classes_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
class Counter:
    value: int

    fn increment(self):
        self.value = self.value + 1
        return self.value

c = Counter(0)
c.increment()
c.increment()
main = c.value
"#,
        )
        .expect("class basic");
    assert_eq!(result, 2);
}

// =============================================================================
// Feature #11-12: Enums and Pattern Matching
// =============================================================================

/// Test Feature #11: Enums - basic
#[test]
fn test_feature_enums_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
enum Color:
    Red
    Green
    Blue

c = Color::Red
main = match c:
    Color::Red => 1
    Color::Green => 2
    Color::Blue => 3
"#,
        )
        .expect("enum basic");
    assert_eq!(result, 1);
}

/// Test Feature #12: Pattern Matching - basic
#[test]
fn test_feature_pattern_matching_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 5
main = match x:
    1 => 10
    5 => 50
    _ => 0
"#,
        )
        .expect("pattern match");
    assert_eq!(result, 50);
}

/// Test Feature #12: Pattern Matching - destructuring
#[test]
fn test_feature_pattern_matching_destructure() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
t = (10, 20)
main = match t:
    (a, b) => a + b
"#,
        )
        .expect("destructure match");
    assert_eq!(result, 30);
}

// =============================================================================
// Feature #17: Lambdas/Closures
// =============================================================================

/// Test Feature #17: Lambdas - basic
#[test]
fn test_feature_lambdas_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
double = \x: x * 2
main = double(21)
"#,
        )
        .expect("lambda");
    assert_eq!(result, 42);
}

/// Test Feature #17: Lambdas with multiple params
#[test]
fn test_feature_lambdas_multi_param() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
add = \a, b: a + b
main = add(10, 5)
"#,
        )
        .expect("lambda multi param");
    assert_eq!(result, 15);
}

// =============================================================================
// Feature #38-42: Option, Tuples, Arrays, Dictionaries
// =============================================================================

/// Test Feature #38: Option Type - Some
#[test]
fn test_feature_option_some() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
opt = Some(42)
main = opt.unwrap()
"#,
        )
        .expect("option some");
    assert_eq!(result, 42);
}

/// Test Feature #38: Option Type - None with default
#[test]
fn test_feature_option_none_default() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
opt = None
main = opt.unwrap_or(99)
"#,
        )
        .expect("option none");
    assert_eq!(result, 99);
}

/// Test Feature #40: Tuple Types
#[test]
fn test_feature_tuple_types() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
t = (1, 2, 3)
main = t[0] + t[1] + t[2]
"#,
        )
        .expect("tuple");
    assert_eq!(result, 6);
}

/// Test Feature #41: Array Types - creation
#[test]
fn test_feature_array_creation() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [10, 20, 30, 40]
main = arr.len()
"#,
        )
        .expect("array creation");
    assert_eq!(result, 4);
}

/// Test Feature #41: Array Types - indexing
#[test]
fn test_feature_array_indexing() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [5, 10, 15]
main = arr[1]
"#,
        )
        .expect("array indexing");
    assert_eq!(result, 10);
}

/// Test Feature #42: Dictionary Types
#[test]
fn test_feature_dict_types() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
d = {"a": 1, "b": 2}
main = d["a"] + d["b"]
"#,
        )
        .expect("dict");
    assert_eq!(result, 3);
}

// =============================================================================
// Feature #62-69: List/Dict Comprehension, Slicing, Negative Indexing, etc.
// =============================================================================

/// Test Feature #62: List Comprehension - basic
#[test]
fn test_feature_list_comprehension_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [1, 2, 3, 4, 5]
squared = [x * x for x in arr]
main = squared[2]
"#,
        )
        .expect("list comprehension");
    assert_eq!(result, 9); // 3 * 3
}

/// Test Feature #62: List Comprehension - with filter
#[test]
fn test_feature_list_comprehension_filter() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [1, 2, 3, 4, 5, 6]
evens = [x for x in arr if x % 2 == 0]
main = evens.len()
"#,
        )
        .expect("list comprehension filter");
    assert_eq!(result, 3); // [2, 4, 6]
}

/// Test Feature #63: Dict Comprehension
#[test]
fn test_feature_dict_comprehension() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [1, 2, 3]
d = {x: x * x for x in arr}
main = d[2]
"#,
        )
        .expect("dict comprehension");
    assert_eq!(result, 4);
}

/// Test Feature #64: Slicing - basic
#[test]
fn test_feature_slicing_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [1, 2, 3, 4, 5]
s = arr[1:4]
main = s.len()
"#,
        )
        .expect("slicing basic");
    assert_eq!(result, 3); // [2, 3, 4]
}

/// Test Feature #65: Negative Indexing
#[test]
fn test_feature_negative_indexing() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [10, 20, 30, 40, 50]
main = arr[-1]
"#,
        )
        .expect("negative indexing");
    assert_eq!(result, 50); // last element
}

/// Test Feature #65: Negative Indexing - second last
#[test]
fn test_feature_negative_indexing_second_last() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
arr = [10, 20, 30, 40, 50]
main = arr[-2]
"#,
        )
        .expect("negative indexing -2");
    assert_eq!(result, 40);
}

/// Test Feature #66: Tuple Unpacking - basic
#[test]
fn test_feature_tuple_unpacking_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
let (a, b, c) = (10, 20, 30)
main = a + b + c
"#,
        )
        .expect("tuple unpacking");
    assert_eq!(result, 60);
}

/// Test Feature #66: Tuple Unpacking - swap
#[test]
fn test_feature_tuple_unpacking_swap() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = 10
b = 20
(a, b) = (b, a)
main = a - b
"#,
        )
        .expect("tuple swap");
    assert_eq!(result, 10); // 20 - 10
}

/// Test Feature #67: Chained Comparisons
#[test]
fn test_feature_chained_comparisons() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 5
main = if 0 < x < 10: 1 else: 0
"#,
        )
        .expect("chained comparison");
    assert_eq!(result, 1);
}

/// Test Feature #67: Chained Comparisons - false
#[test]
fn test_feature_chained_comparisons_false() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 15
main = if 0 < x < 10: 1 else: 0
"#,
        )
        .expect("chained comparison false");
    assert_eq!(result, 0);
}

/// Test Feature #68: Context Managers - basic with statement
#[test]
fn test_feature_context_managers() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
class Resource:
    value: int

    fn __enter__(self):
        return self.value + 10

    fn __exit__(self, exc):
        pass

r = Resource(5)
result = 0
with r as v:
    result = v

main = result
"#,
        )
        .expect("context manager");
    assert_eq!(result, 15); // 5 + 10
}

/// Test Feature #69: Spread Operators - array spread
#[test]
fn test_feature_spread_array() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = [1, 2]
b = [3, 4]
c = [*a, *b]
main = c.len()
"#,
        )
        .expect("array spread");
    assert_eq!(result, 4);
}

/// Test Feature #69: Spread Operators - dict spread
#[test]
fn test_feature_spread_dict() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
d1 = {"a": 1}
d2 = {"b": 2}
d3 = {**d1, **d2}
main = d3["a"] + d3["b"]
"#,
        )
        .expect("dict spread");
    assert_eq!(result, 3);
}

