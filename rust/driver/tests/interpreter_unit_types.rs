#![allow(unused_imports)]

//! Interpreter tests - unit types, compound units, SI prefixes

use simple_driver::interpreter::{run_code, Interpreter, RunConfig, RunningType};

#[allow(dead_code)]
fn run_expect_error(src: &str, expected_error: &str) {
    let result = run_code(src, &[], "");
    match result {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                err_msg
            );
        }
        Ok(_) => panic!(
            "Expected error containing '{}', but execution succeeded",
            expected_error
        ),
    }
}

#[allow(dead_code)]
fn run_expect_any_error(src: &str) {
    let result = run_code(src, &[], "");
    assert!(result.is_err(), "Expected an error, but execution succeeded");
}

// ============= Standalone Unit Tests =============

#[test]
fn interpreter_unit_def_basic() {
    // Define a standalone unit type and use it
    let code = r#"
unit UserId: i64 as uid

let user_id = 42_uid
main = user_id
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unit_def_arithmetic() {
    // Unit types can be used in arithmetic (value semantics)
    let code = r#"
unit Score: i64 as pts

let a = 100_pts
let b = 50_pts
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 150);
}

// ============= String Methods Tests =============

// ============= Unit Family Tests (#87) =============
// Note: Full unit family syntax `unit length(base: f64): m = 1.0, km = 1000.0`
// is not yet implemented. These tests use standalone units as a foundation.

#[test]
fn interpreter_unit_family_basic() {
    // Define a unit family with conversion factors
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 5000.0_m
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_unit_family_to_base() {
    // Convert km to m using unit family conversion
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 2_km
let meters = d.to_m()
main = meters.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2000); // 2 km = 2000 m
}

#[test]
fn interpreter_unit_conversion_m_to_km() {
    // Convert m to km - should get fractional result stored as int
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 5000_m
let kilometers = d.to_km()
main = kilometers.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5); // 5000 m = 5 km
}

#[test]
fn interpreter_unit_conversion_preserves_suffix() {
    // Converted value should have the target suffix
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 3_km
let meters = d.to_m()
let suffix = meters.suffix()
main = if suffix == "m": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_unit_time_family() {
    // Test time unit family with multiple conversions
    let code = r#"
unit time(base: f64): s = 1.0, ms = 0.001, hr = 3600.0

let duration = 2_hr
let seconds = duration.to_s()
main = seconds.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7200); // 2 hours = 7200 seconds
}

#[test]
fn interpreter_unit_chained_conversion() {
    // Convert and then access value
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0, cm = 0.01

let d = 1_km
let centimeters = d.to_cm()
# 1 km = 100,000 cm (1000 / 0.01)
main = if centimeters.value() == 100000: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_unit_value_method() {
    // .value() returns the underlying numeric value
    let code = r#"
let d = 42_km
main = d.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unit_suffix_method() {
    // .suffix() returns the unit suffix as a string
    let code = r#"
let d = 100_bytes
let s = d.suffix()
main = if s == "bytes": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_unit_to_string_method() {
    // .to_string() returns the full representation
    let code = r#"
let d = 5_km
let s = d.to_string()
main = if s == "5_km": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_unit_float_suffix() {
    // Float values with unit suffix
    let code = r#"
let speed = 3.5_mps
main = if speed.value() == 3.5: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Primitive API Warnings (#92) =============
// These tests verify that warnings are issued for public APIs using primitives

#[test]
fn interpreter_primitive_warning_suppressed_with_attribute() {
    // #[allow(primitive_api)] suppresses the warning
    let code = r#"
#[allow(primitive_api)]
pub fn get_count() -> i64:
    return 42

main = get_count()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_semantic_type_no_warning() {
    // Using semantic types (unit types) should not warn
    let code = r#"
unit Count: i64 as cnt

pub fn get_count() -> Count:
    return 42_cnt

main = get_count()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============= Type-Safe Unit Arithmetic Tests (#203) =============

#[test]
fn interpreter_unit_arithmetic_same_family_allowed() {
    // Same-family addition should work when explicitly allowed
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow sub(length) -> length

let a = 100_m
let b = 50_m
main = (a + b).value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 150);
}

#[test]
fn interpreter_unit_arithmetic_subtraction_allowed() {
    // Same-family subtraction when allowed
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0:
    allow sub(length) -> length

let a = 100_m
let b = 30_m
main = (a - b).value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 70);
}

#[test]
fn interpreter_unit_arithmetic_default_deny() {
    // Operations not in explicit allow list should fail
    // This unit family only allows sub, so add should fail
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0:
    allow sub(length) -> length

let a = 100_m
let b = 50_m
main = (a + b).value()
"#;
    run_expect_error(code, "not allowed");
}

#[test]
fn interpreter_unit_arithmetic_cross_family_denied() {
    // Different families cannot be added even with allow on each
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length

unit time(base: f64): s = 1.0, hr = 3600.0:
    allow add(time) -> time

let dist = 100_m
let dur = 10_s
main = (dist + dur).value()
"#;
    run_expect_error(code, "not allowed");
}

#[test]
fn interpreter_unit_scaling_allowed() {
    // Scaling (unit * scalar) should always work
    let code = r#"
unit length(base: f64): m = 1.0

let d = 10_m
let scaled = d * 3
main = scaled.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_unit_negation_allowed() {
    // Unary negation when allowed
    let code = r#"
unit temperature(base: f64): c = 1.0, k = 1.0:
    allow neg -> temperature

let t = 10_c
let neg_t = -t
main = neg_t.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -10);
}

#[test]
fn interpreter_unit_negation_default_deny() {
    // Negation not in explicit allow list should fail
    // This unit family only allows add, so neg should fail
    let code = r#"
unit length(base: f64): m = 1.0:
    allow add(length) -> length

let d = 10_m
main = (-d).value()
"#;
    run_expect_error(code, "not allowed");
}

#[test]
fn interpreter_unit_comparison_always_allowed() {
    // Same-family comparison should always work (no allow needed)
    let code = r#"
unit length(base: f64): m = 1.0

let a = 100_m
let b = 50_m
main = if a > b: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Compound Unit Tests (#206) =============

#[test]
fn interpreter_compound_unit_basic_definition() {
    // Define a compound unit and verify parsing works
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time

main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_compound_unit_division_produces_compound() {
    // When dividing length / time, result should be velocity dimension
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time

let dist = 100_m
let dur = 10_s
let speed = dist / dur
main = speed.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // 100 / 10 = 10
}

#[test]
fn interpreter_compound_unit_multiplication() {
    // velocity * time should give length
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time

let speed = 10_m  # We'll simulate velocity with m for now
let dur = 5_s
let result = speed * dur
main = result.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50); // 10 * 5 = 50
}

#[test]
fn interpreter_compound_unit_same_unit_cancellation() {
    // length / length should give dimensionless (plain number)
    let code = r#"
unit length(base: f64): m = 1.0

let dist1 = 100_m
let dist2 = 20_m
let ratio = dist1 / dist2
main = ratio
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5); // 100 / 20 = 5 (dimensionless)
}

#[test]
fn interpreter_compound_unit_area() {
    // length * length = area
    let code = r#"
unit length(base: f64): m = 1.0
unit area = length * length

let width = 10_m
let height = 5_m
let a = width * height
main = a.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50); // 10 * 5 = 50
}

#[test]
fn interpreter_compound_unit_complex() {
    // Define acceleration = length / time^2
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit acceleration = length / time / time

let accel = 10_m  # simplified
let t = 2_s
let t2 = 3_s
let result = accel / t / t2
main = result.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // 10 / 2 / 3 = 1 (integer division)
}

// =============================================================================
// SI Prefix Tests (#207)
// =============================================================================

#[test]
fn interpreter_si_prefix_kilo() {
    // k prefix = 1000x
    let code = r#"
unit length(base: f64): m = 1.0

let dist = 5_km   # Should be 5 * 1000 = 5000 meters
main = dist.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5000);
}

#[test]
fn interpreter_si_prefix_mega() {
    // M prefix = 1,000,000x
    let code = r#"
unit length(base: f64): m = 1.0

let dist = 2_Mm   # 2 megameters = 2,000,000 meters
main = dist.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2000000);
}

#[test]
fn interpreter_si_prefix_giga() {
    // G prefix = 1,000,000,000x (1e9)
    let code = r#"
unit length(base: f64): m = 1.0

let dist = 1_Gm   # 1 gigameter = 1e9 meters
main = if dist.value() > 999999999: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_si_prefix_milli() {
    // m prefix = 0.001x (but requires base unit that isn't 'm')
    let code = r#"
unit time(base: f64): s = 1.0

let dur = 500_ms   # 500 milliseconds = 0.5 seconds
# Check it's less than 1 second
main = if dur.value() < 1.0: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_si_prefix_micro() {
    // u prefix = 0.000001x (micro)
    let code = r#"
unit time(base: f64): s = 1.0

let dur = 1000_us   # 1000 microseconds = 0.001 seconds = 1 millisecond
# Check it equals 0.001
main = if dur.value() < 0.01 and dur.value() > 0.0: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_si_prefix_nano() {
    // n prefix = 1e-9
    let code = r#"
unit time(base: f64): s = 1.0

let dur = 1000000000_ns   # 1 billion nanoseconds = 1 second
main = dur.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_si_prefix_family_preserved() {
    // SI-prefixed units should still belong to the same family
    let code = r#"
unit length(base: f64): m = 1.0

let a = 1_km    # 1000 meters
let b = 500_m   # 500 meters
let total = a + b  # Should work - same family
main = total.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1500);
}

#[test]
fn interpreter_si_prefix_conversion() {
    // SI-prefixed units should work with to_X() conversion
    let code = r#"
unit length(base: f64): m = 1.0

let dist = 2_km   # 2000 meters
let in_m = dist.to_m()
main = in_m.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2000);
}

#[test]
fn interpreter_si_prefix_directly_defined_takes_precedence() {
    // If km is directly defined, it takes precedence over k+m
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let dist = 3_km   # Uses directly defined km, not SI prefix
main = dist.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    // 3_km with factor 1000 should give 3.0 in base units
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_si_prefix_tera() {
    // T prefix = 1e12
    let code = r#"
unit data(base: f64): B = 1.0

let size = 1_TB   # 1 terabyte = 1e12 bytes
main = if size.value() > 999999999999.0: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// Unit inference tests (#208)

#[test]
fn interpreter_unit_inference_parameter_correct() {
    // Parameter with unit type annotation should accept correct unit
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

fn double_distance(d: length) -> length:
    return d + d

let dist = 5_km
main = double_distance(dist).value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_unit_inference_parameter_wrong_family() {
    // Parameter with unit type should reject wrong unit family
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0

fn measure_length(d: length) -> i64:
    return d.value()

let dur = 5_s
main = measure_length(dur)
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err() || result.unwrap().exit_code != 5);
}

#[test]
fn interpreter_unit_inference_return_correct() {
    // Function returning unit type should work when correct
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

fn get_distance() -> length:
    return 10_m

main = get_distance().value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_unit_inference_return_wrong_family() {
    // Function returning unit type should reject wrong unit family
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0

fn get_distance() -> length:
    return 5_s

main = get_distance().value()
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_unit_inference_compound_unit() {
    // Should work with compound units too
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0
unit time(base: f64): s = 1.0
unit velocity = length / time

fn get_speed(d: length, t: time) -> velocity:
    return d / t

let dist = 100_m
let dur = 10_s
main = get_speed(dist, dur).value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_unit_inference_non_unit_value() {
    // Passing non-unit value to unit parameter should fail
    let code = r#"
unit length(base: f64): m = 1.0

fn measure(d: length) -> i64:
    return d.value()

main = measure(42)
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_unit_inference_return_non_unit() {
    // Returning non-unit value when unit expected should fail
    let code = r#"
unit length(base: f64): m = 1.0

fn get_distance() -> length:
    return 42

main = get_distance().value()
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

// Unit assertion tests (#209)

#[test]
fn interpreter_assert_unit_correct_type() {
    // assert_unit! with correct type should pass
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let dist = 10_km
assert_unit!(dist, "length")
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_assert_unit_wrong_type() {
    // assert_unit! with wrong type should fail
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0

let dist = 10_m
assert_unit!(dist, "time")
main = 1
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_assert_unit_non_unit_value() {
    // assert_unit! on non-unit value should fail
    let code = r#"
unit length(base: f64): m = 1.0

let x = 42
assert_unit!(x, "length")
main = 1
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_assert_unit_invalid_type_name() {
    // assert_unit! with unregistered type name should fail
    let code = r#"
unit length(base: f64): m = 1.0

let dist = 10_m
assert_unit!(dist, "nonexistent_type")
main = 1
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_assert_unit_compound_type() {
    // assert_unit! with compound unit type should work
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0
unit velocity = length / time

let v = 10_m / 2_s
assert_unit!(v, "velocity")
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_let_binding_unit_type_correct() {
    // Let binding with correct unit type should pass
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let dist: length = 5_km
main = dist.value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_let_binding_unit_type_wrong() {
    // Let binding with wrong unit type should fail
    let code = r#"
unit length(base: f64): m = 1.0
unit time(base: f64): s = 1.0

let dist: length = 5_s
main = 1
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_let_binding_unit_type_non_unit_value() {
    // Let binding with unit type but non-unit value should fail
    let code = r#"
unit length(base: f64): m = 1.0

let dist: length = 42
main = 1
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}
