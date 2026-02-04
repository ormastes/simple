//! Interpreter Performance Benchmarks
//!
//! Benchmarks for measuring interpreter performance across key operations:
//! - Variable access (local, global, closure)
//! - Function calls (direct, closure, method)
//! - Collection operations (array, dict)
//! - Control flow (if, match, loop)
//!
//! These benchmarks establish a performance baseline and help identify
//! optimization opportunities.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;
use std::time::Duration;

/// Helper to parse and evaluate Simple code
fn run_code(code: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut parser = Parser::new(code);
    let module = parser.parse()?;
    let result = evaluate_module(&module.items)?;
    Ok(result)
}

/// Benchmark variable access patterns
fn bench_variable_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("variable_access");

    // Local variable access (most common case)
    group.bench_function("local_var", |b| {
        let code = r#"
fn test_local():
    val x = 42
    val y = x + 1
    val z = y * 2
    z
test_local()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Global variable access
    group.bench_function("global_var", |b| {
        let code = r#"
val GLOBAL_X = 42

fn test_global():
    val y = GLOBAL_X + 1
    val z = y * 2
    z
test_global()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Closure variable access
    group.bench_function("closure_var", |b| {
        let code = r#"
fn make_closure():
    val x = 42
    fn inner():
        x + 1
    inner

val closure = make_closure()
closure()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    group.finish();
}

/// Benchmark function call patterns
fn bench_function_calls(c: &mut Criterion) {
    let mut group = c.benchmark_group("function_calls");

    // Direct function call
    group.bench_function("direct_call", |b| {
        let code = r#"
fn add(a, b):
    a + b

fn test():
    val result = 0
    for i in 0..10:
        result = result + add(i, 1)
    result
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Closure call
    group.bench_function("closure_call", |b| {
        let code = r#"
fn test():
    val adder = \x: x + 1
    val result = 0
    for i in 0..10:
        result = result + adder(i)
    result
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Method call
    group.bench_function("method_call", |b| {
        let code = r#"
class Counter:
    value: i64

    fn increment():
        self.value + 1

fn test():
    val counter = Counter(value: 0)
    val result = 0
    for i in 0..10:
        result = result + counter.increment()
    result
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Recursive call (fibonacci)
    group.bench_function("recursive_call", |b| {
        let code = r#"
fn fib(n):
    if n <= 1:
        n
    else:
        fib(n - 1) + fib(n - 2)

fib(15)
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    group.finish();
}

/// Benchmark collection operations
fn bench_collections(c: &mut Criterion) {
    let mut group = c.benchmark_group("collections");

    // Array access
    group.bench_function("array_access", |b| {
        let code = r#"
fn test():
    val arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    val sum = 0
    for i in 0..10:
        sum = sum + arr[i]
    sum
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Dict lookup
    group.bench_function("dict_lookup", |b| {
        let code = r#"
fn test():
    val dict = {"a": 1, "b": 2, "c": 3, "d": 4, "e": 5}
    val sum = 0
    for key in ["a", "b", "c", "d", "e"]:
        sum = sum + dict[key]
    sum
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Array iteration
    group.bench_function("array_iteration", |b| {
        let code = r#"
fn test():
    val arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    val sum = 0
    for x in arr:
        sum = sum + x
    sum
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    group.finish();
}

/// Benchmark control flow patterns
fn bench_control_flow(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow");

    // If-else
    group.bench_function("if_else", |b| {
        let code = r#"
fn test():
    val sum = 0
    for i in 0..100:
        if i % 2 == 0:
            sum = sum + i
        else:
            sum = sum - i
    sum
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // Match expression
    group.bench_function("match_expr", |b| {
        let code = r#"
fn classify(x):
    match x % 3:
        0: "zero"
        1: "one"
        _: "two"

fn test():
    val count = 0
    for i in 0..100:
        val result = classify(i)
        count = count + 1
    count
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    // While loop
    group.bench_function("while_loop", |b| {
        let code = r#"
fn test():
    var i = 0
    var sum = 0
    while i < 100:
        sum = sum + i
        i = i + 1
    sum
test()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    group.finish();
}

/// Benchmark composite workloads
fn bench_composite(c: &mut Criterion) {
    let mut group = c.benchmark_group("composite");
    group.measurement_time(Duration::from_secs(10));

    // Typical script workload: mix of operations
    group.bench_function("typical_script", |b| {
        let code = r#"
fn factorial(n):
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

fn process_array(arr):
    val result = []
    for x in arr:
        if x % 2 == 0:
            result.push(factorial(x / 2))
        else:
            result.push(x)
    result

fn main():
    val input = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    val processed = process_array(input)
    val sum = 0
    for x in processed:
        sum = sum + x
    sum

main()
"#;
        b.iter(|| {
            let result = run_code(black_box(code));
            black_box(result)
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_variable_access,
    bench_function_calls,
    bench_collections,
    bench_control_flow,
    bench_composite
);
criterion_main!(benches);
