//! Feature tests: Advanced features and public function coverage
//! Features #62-95 and public API coverage

#![allow(unused_imports, unused_variables, deprecated)]

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

/// Helper to run source and expect a compile/parse error containing a substring.
#[allow(dead_code)]
fn run_expect_compile_error(src: &str, expected_error: &str) {
    let runner = Runner::new_no_gc();
    let result = runner.run_source(src);
    match result {
        Err(e) => {
            assert!(
                e.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                e
            );
        }
        Ok(code) => panic!(
            "Expected compile error containing '{}', but execution succeeded with code {}",
            expected_error, code
        ),
    }
}

// =============================================================================
// Public Function Coverage - ExecCore methods (feature tests)
// =============================================================================

/// Test ExecCore::new (feature tests)
#[test]
fn test_exec_core_new_feature() {
    use simple_driver::exec_core::ExecCore;
    let core = ExecCore::new();
    // Should create successfully
    let result = core.run_source_in_memory("main = 1");
    assert!(result.is_ok());
}

/// Test ExecCore::new_no_gc (feature tests)
#[test]
fn test_exec_core_new_no_gc_feature() {
    use simple_driver::exec_core::ExecCore;
    let core = ExecCore::new_no_gc();
    let result = core.run_source_in_memory("main = 42");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
}

/// Test ExecCore::compile_to_memory (feature tests)
#[test]
fn test_exec_core_compile_to_memory_feature() {
    use simple_driver::exec_core::ExecCore;
    let core = ExecCore::new_no_gc();
    let smf_bytes = core.compile_to_memory("main = 77").expect("compile ok");
    assert!(!smf_bytes.is_empty());
    // Run the compiled bytes
    let result = core.run_smf_from_memory(&smf_bytes).expect("run ok");
    assert_eq!(result, 77);
}

/// Test ExecCore::collect_gc (feature tests)
#[test]
fn test_exec_core_collect_gc_feature() {
    use simple_driver::exec_core::ExecCore;
    let core = ExecCore::new();
    core.run_source_in_memory("main = 1").expect("run ok");
    // Should not panic
    core.collect_gc();
}

// =============================================================================
// Public Function Coverage - Additional Interpreter methods (feature tests)
// =============================================================================

/// Test Interpreter::run_simple (feature tests)
#[test]
fn test_interpreter_run_simple_feature() {
    let interp = Interpreter::new_no_gc();
    let result = interp.run_simple("main = 123");
    assert!(result.is_ok());
    // run_simple returns RunResult, access exit_code
    assert_eq!(result.unwrap().exit_code, 123);
}

/// Test Interpreter::gc (feature tests)
#[test]
fn test_interpreter_gc_method_feature() {
    let interp = Interpreter::new();
    let _ = interp.run_simple("main = 1");
    // gc() should not panic
    interp.gc();
}

// =============================================================================
// Public Function Coverage - Runner additional methods (feature tests)
// =============================================================================

/// Test Runner::with_gc_runtime (feature tests)
#[test]
fn test_runner_with_gc_runtime_feature() {
    use simple_runtime::gc::GcRuntime;
    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);
    let result = runner.run_source("main = 55");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 55);
}

/// Test Runner::new_with_gc_logging (feature tests)
#[test]
fn test_runner_new_with_gc_logging_feature() {
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 33");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 33);
}

/// Test Runner::gc (feature tests)
#[test]
fn test_runner_gc_method_feature() {
    let runner = Runner::new();
    runner.run_source("main = 1").expect("run ok");
    // gc() should not panic
    runner.gc();
}

// =============================================================================
// Feature #71-80: Attributes, Result Type, ? Operator, Match Guards, etc.
// System Tests for Class/Struct Coverage
// =============================================================================

/// Feature #71: Attributes - #[inline] on function
#[test]
fn test_feature_71_attribute_inline() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
#[inline]
fn fast_add(a, b):
    return a + b

main = fast_add(20, 22)
"#,
        )
        .expect("attribute inline");
    assert_eq!(result, 42);
}

/// Feature #71: Attributes - #[deprecated] on function
#[test]
fn test_feature_71_attribute_deprecated() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
#[deprecated]
fn old_function(x):
    return x * 2

main = old_function(10)
"#,
        )
        .expect("attribute deprecated");
    assert_eq!(result, 20);
}

/// Feature #71: Attributes - #[deprecated = "message"]
#[test]
fn test_feature_71_attribute_with_value() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
#[deprecated = "use new_api instead"]
fn legacy_api(x):
    return x + 1

main = legacy_api(5)
"#,
        )
        .expect("attribute with value");
    assert_eq!(result, 6);
}

/// Feature #71: Multiple attributes on same item
#[test]
fn test_feature_71_multiple_attributes() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
#[inline]
#[deprecated]
fn optimized_legacy(x):
    return x * x

main = optimized_legacy(6)
"#,
        )
        .expect("multiple attributes");
    assert_eq!(result, 36);
}

/// Feature #72: Result Type - Ok variant
#[test]
fn test_feature_72_result_ok() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
res = Ok(42)
main = res.unwrap()
"#,
        )
        .expect("result ok");
    assert_eq!(result, 42);
}

/// Feature #72: Result Type - Err variant with unwrap_or
#[test]
fn test_feature_72_result_err_unwrap_or() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
res = Err("error message")
main = res.unwrap_or(99)
"#,
        )
        .expect("result err");
    assert_eq!(result, 99);
}

/// Feature #72: Result Type - is_ok check
#[test]
fn test_feature_72_result_is_ok() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
res = Ok(10)
x = 0
if res.is_ok():
    x = 1
main = x
"#,
        )
        .expect("result is_ok");
    assert_eq!(result, 1);
}

/// Feature #72: Result Type - is_err check
#[test]
fn test_feature_72_result_is_err() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
res = Err("oops")
x = 0
if res.is_err():
    x = 1
main = x
"#,
        )
        .expect("result is_err");
    assert_eq!(result, 1);
}

/// Feature #72: Result Type - from function
#[test]
fn test_feature_72_result_from_function() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

r = safe_divide(20, 4)
main = r.unwrap()
"#,
        )
        .expect("result from function");
    assert_eq!(result, 5);
}

/// Feature #73: ? Operator - basic propagation
#[test]
fn test_feature_73_question_operator() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn may_fail(x) -> Res[int, str]:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    val = may_fail(x)?
    return Ok(val + 1)

res = caller(5)
main = res.unwrap()
"#,
        )
        .expect("? operator");
    assert_eq!(result, 11); // 5 * 2 + 1
}

/// Feature #74: Match Guards - basic if guard
#[test]
fn test_feature_74_match_guard_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
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
"#,
        )
        .expect("match guard");
    assert_eq!(result, 1);
}

/// Feature #74: Match Guards - negative value
#[test]
fn test_feature_74_match_guard_negative() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
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
"#,
        )
        .expect("match guard negative");
    assert_eq!(result, -1);
}

/// Feature #75: If Let - Some pattern
#[test]
fn test_feature_75_if_let_some() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
opt = Some(42)
res = 0
if let Some(x) = opt:
    res = x
main = res
"#,
        )
        .expect("if let some");
    assert_eq!(result, 42);
}

/// Feature #75: If Let - None with else
#[test]
fn test_feature_75_if_let_none_else() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
opt = None
res = 0
if let Some(x) = opt:
    res = x
else:
    res = -1
main = res
"#,
        )
        .expect("if let none");
    assert_eq!(result, -1);
}

/// Feature #75: While Let - basic loop
#[test]
fn test_feature_75_while_let() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn next_item(n):
    if n > 0:
        return Some(n)
    return None

counter = 3
sum = 0
while let Some(val) = next_item(counter):
    sum = sum + val
    counter = counter - 1
main = sum
"#,
        )
        .expect("while let");
    assert_eq!(result, 6); // 3 + 2 + 1
}

/// Feature #76: Derive Macros - Debug derive
#[test]
fn test_feature_76_derive_debug() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
#[derive(Debug)]
struct Point:
    x: int
    y: int

p = Point(10, 20)
main = p.x + p.y
"#,
        )
        .expect("derive debug");
    assert_eq!(result, 30);
}

/// Feature #77: Move Closures
#[test]
fn test_feature_77_move_closure() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
x = 10
closure = move \: x * 2
main = closure()
"#,
        )
        .expect("move closure");
    assert_eq!(result, 20);
}

/// Feature #80: Or Patterns in match
#[test]
fn test_feature_80_or_pattern() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn classify(x):
    match x:
        1 | 2 | 3 =>
            return 10
        4 | 5 =>
            return 20
        _ =>
            return 0
    return -1

main = classify(2)
"#,
        )
        .expect("or pattern");
    assert_eq!(result, 10);
}

// =============================================================================
// Feature Tests #81-95
// =============================================================================

/// Feature #81: Range Patterns in match
#[test]
fn test_feature_81_range_pattern() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn grade(score):
    match score:
        90..100 =>
            return 4  # A
        80..90 =>
            return 3  # B
        70..80 =>
            return 2  # C
        0..70 =>
            return 1  # D/F
        _ =>
            return 0
    return -1

main = grade(85)
"#,
        )
        .expect("range pattern");
    assert_eq!(result, 3);
}

/// Feature #81: Range patterns - inclusive range
#[test]
fn test_feature_81_range_pattern_inclusive() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn classify(x):
    match x:
        0..=5 =>
            return 1
        6..=10 =>
            return 2
        _ =>
            return 0

main = classify(5)
"#,
        )
        .expect("inclusive range pattern");
    assert_eq!(result, 1);
}

/// Feature #82: Auto-Forwarding Properties - get_ prefix
#[test]
fn test_feature_82_auto_forwarding_get() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
class Counter:
    fn get_count(self) -> int:
        return self._count

    fn increment(self):
        self._count = self._count + 1

c = Counter()
c.increment()
c.increment()
main = c.count
"#,
        )
        .expect("auto-forwarding get");
    assert_eq!(result, 2);
}

/// Feature #82: Auto-Forwarding Properties - set_ prefix
#[test]
fn test_feature_82_auto_forwarding_set() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
class Value:
    fn get_value(self) -> int:
        return self._value

    fn set_value(self, v: int):
        self._value = v

v = Value()
v.value = 42
main = v.value
"#,
        )
        .expect("auto-forwarding set");
    assert_eq!(result, 42);
}

/// Feature #82: Auto-Forwarding Properties - is_ prefix
#[test]
fn test_feature_82_auto_forwarding_is() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
class Toggle:
    fn is_enabled(self) -> bool:
        return self._enabled

    fn enable(self):
        self._enabled = true

t = Toggle()
t.enable()
main = if t.enabled: 1 else: 0
"#,
        )
        .expect("auto-forwarding is");
    assert_eq!(result, 1);
}

/// Feature #83: Isolated Threads - spawn_isolated
#[test]
fn test_feature_83_spawn_isolated() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
const MULTIPLIER = 10

fn worker(x: int) -> int:
    return x * MULTIPLIER

handle = spawn_isolated(worker, 5)
res = handle.join()
main = res
"#,
        )
        .expect("spawn_isolated");
    assert_eq!(result, 50);
}

/// Feature #83: Isolated Threads with channel
#[test]
fn test_feature_83_isolated_with_channel() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
fn producer(ch: Channel[int]):
    ch.send(42)

fn consumer(ch: Channel[int]) -> int:
    return ch.recv()

ch = Channel[int]()
spawn_isolated(producer, ch)
main = consumer(ch)
"#,
        )
        .expect("isolated with channel");
    assert_eq!(result, 42);
}

/// Feature #84: Channel Types - basic send/recv
#[test]
fn test_feature_84_channel_basic() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
ch = Channel[int]()
ch.send(100)
main = ch.recv()
"#,
        )
        .expect("channel basic");
    assert_eq!(result, 100);
}

/// Feature #84: Channel Types - buffered channel
#[test]
fn test_feature_84_channel_buffered() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
ch = Channel[int](buffer=3)
ch.send(1)
ch.send(2)
ch.send(3)
main = ch.recv() + ch.recv() + ch.recv()
"#,
        )
        .expect("buffered channel");
    assert_eq!(result, 6);
}

/// Feature #84: Channel Types - try_recv
#[test]
fn test_feature_84_channel_try_recv() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
ch = Channel[int]()
# No sender, try_recv should return None
res = ch.try_recv()
main = if res.is_none(): 1 else: 0
"#,
        )
        .expect("channel try_recv");
    assert_eq!(result, 1);
}

/// Feature #85: Send/Copy Traits
#[test]
fn test_feature_85_send_trait() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
# int is Send + Copy
fn thread_safe(x: Send) -> int:
    return x

main = thread_safe(42)
"#,
        )
        .expect("send trait");
    assert_eq!(result, 42);
}

/// Feature #86: Thread Pool
#[test]
fn test_feature_86_thread_pool() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
pool = ThreadPool(workers=4)

fn double(x: int) -> int:
    return x * 2

futures = [pool.submit(double, i) for i in [1, 2, 3, 4]]
results = [f.get() for f in futures]
main = results[0] + results[1] + results[2] + results[3]
"#,
        )
        .expect("thread pool");
    assert_eq!(result, 20);
}

/// Feature #87: Unit Types - basic unit definition
/// NOTE: This syntax (indented block with typed variable) is not yet implemented.
/// The simpler inline syntax `unit length(base: f64): m = 1.0, km = 1000.0` works.
#[test]
fn test_feature_87_unit_types_basic_not_yet_implemented() {
    // This test documents the intended future syntax with indented block
    // Currently produces a parse error - will be enabled when full syntax is implemented
    run_expect_compile_error(
        r#"
unit length(base: f64):
    m = 1.0
    km = 1000.0
    cm = 0.01

distance: length = 5_km
main = int(distance.to_m())
"#,
        "parse", // Expects parse error for typed variable syntax "distance: length = ..."
    );
}

/// Feature #87: Unit Types - conversion
#[test]
fn test_feature_87_unit_types_conversion() {
    let runner = Runner::new_no_gc();
    let source = r#"
unit length(base: f64):
    m = 1.0
    km = 1000.0

a = 2_km
main = a.to_m()
"#;
    let result = runner.run_source(source).expect("unit conversion");
    assert_eq!(result, 2000);
}

/// Feature #88: Literal Suffixes
#[test]
fn test_feature_88_literal_suffix_to_m() {
    let runner = Runner::new_no_gc();
    let source = r#"
unit length(base: f64): m = 1.0, km = 1000.0

distance = 100_km
main = distance.to_m()
"#;
    let result = runner.run_source(source).expect("literal suffix conversion");
    assert_eq!(result, 100000);
}

/// Feature #89: Composite Units
#[test]
fn test_feature_89_composite_units() {
    let runner = Runner::new_no_gc();
    let source = r#"
unit length(base: f64): m = 1.0, km = 1000.0
unit time(base: f64): s = 1.0, hr = 3600.0

unit velocity = length / time

speed = 100_km / 1_hr
main = 1
"#;
    let result = runner.run_source(source).expect("composite units");
    assert_eq!(result, 1);
}

/// Feature #90: Composite Type Inference
#[test]
fn test_feature_90_composite_type_inference() {
    let runner = Runner::new_no_gc();
    let source = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time

distance = 100_m
duration = 10_s
speed = distance / duration
main = 1
"#;
    let result = runner.run_source(source).expect("composite type inference");
    assert_eq!(result, 1);
}

/// Feature #91: Standalone Units
/// NOTE: Typed variable syntax `user_id: UserId = ...` not yet implemented
#[test]
fn test_feature_91_standalone_units_not_yet_implemented() {
    // Typed variable declaration syntax is not yet supported
    run_expect_compile_error(
        r#"
unit UserId: i64 as uid

user_id: UserId = 12345_uid
main = int(user_id)
"#,
        "parse", // Expects parse error for typed variable syntax
    );
}

/// Feature #91: Standalone Units - type safety
/// NOTE: int() cast and UserId type in function signature not yet fully implemented
#[test]
fn test_feature_91_standalone_units_type_safety_not_yet_implemented() {
    // int() cast and unit types in function parameters not fully working
    run_expect_compile_error(
        r#"
unit UserId: i64 as uid
unit OrderId: i64 as oid

fn get_user(id: UserId) -> int:
    return int(id)

user = 42_uid
main = get_user(user)
"#,
        "int", // Expects error for int() cast or type mismatch
    );
}

/// Feature #93: Hexadecimal Literals
#[test]
fn test_feature_93_hex_literals() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = 0xFF
b = 0x10
main = a + b
"#,
        )
        .expect("hex literals");
    assert_eq!(result, 271); // 255 + 16
}

/// Feature #93: Hexadecimal Literals - mixed case
#[test]
fn test_feature_93_hex_literals_mixed_case() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = 0xABcd
b = 0XEF
main = a + b
"#,
        )
        .expect("hex mixed case");
    // 0xABcd = 43981, 0xEF = 239, total = 44220
    assert_eq!(result, 44220);
}

/// Feature #94: Binary Literals
#[test]
fn test_feature_94_binary_literals() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = 0b1010
b = 0b0101
main = a + b
"#,
        )
        .expect("binary literals");
    assert_eq!(result, 15); // 10 + 5
}

/// Feature #94: Binary Literals with underscores
#[test]
fn test_feature_94_binary_literals_underscores() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
flags = 0b1111_0000
main = flags
"#,
        )
        .expect("binary with underscores");
    assert_eq!(result, 240);
}

/// Feature #95: Octal Literals
#[test]
fn test_feature_95_octal_literals() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
a = 0o755
b = 0o10
main = a + b
"#,
        )
        .expect("octal literals");
    assert_eq!(result, 501); // 493 + 8
}

/// Feature #95: Octal Literals - permission style
#[test]
fn test_feature_95_octal_permission() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source(
            r#"
# Unix permission style
read_write_exec = 0o777
read_only = 0o444
main = read_write_exec - read_only
"#,
        )
        .expect("octal permissions");
    assert_eq!(result, 219); // 511 - 292
}
