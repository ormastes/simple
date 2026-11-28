//! Regression tests for the seed-JIT print/interpolation sinks of a typed
//! float optional (`f64?` / `f32?`).
//!
//! Bug: `doc/08_tracking/bug/seed_jit_f64_option_some_print_sink_reads_raw_payload_as_value_2026-11-27`
//! `val c: f64? = Some(0.1); print c` formatted the optional's one-word form
//! as if it were always the legacy flat raw-bits payload, so the print sink
//! (`rt_opt_f64_to_string`) bit-cast the escaping Option enum's heap address
//! into a denormal, and the interpolation sink fell back to `<enum@0x...>`.
//! The interpreter prints `Option::Some(0.1)` for both. These tests pin every
//! one-word form a typed float optional escapes to the sinks in
//! (`mir/float_option_inline.rs`) through both sinks; the expected strings
//! are the interpreter's exact oracles.

use simple_runtime::value::heap::{get_typed_ptr, HeapObjectType};
use simple_runtime::value::{RuntimeString, RuntimeValue};
use simple_runtime::{rt_opt_f64_to_string, rt_opt_f64_value_to_string, rt_option_float_pack};

fn render(s: RuntimeValue) -> String {
    let ptr = get_typed_ptr::<RuntimeString>(s, HeapObjectType::String).expect("a string RuntimeValue");
    unsafe { String::from_utf8_lossy((*ptr).as_bytes()).into_owned() }
}

/// Every one-word form a typed float optional reaches the print/interpolation
/// sinks in, built exactly the way the producers build them
/// (`rt_option_float_pack` is the escape-time boxing the inline pass uses).
fn word_forms(value: f64) -> Vec<(&'static str, RuntimeValue)> {
    vec![
        ("nil", RuntimeValue::NIL),
        ("flat-raw-bits", RuntimeValue::from_raw(value.to_bits())),
        ("flat-boxed-float", RuntimeValue::from_float(value)),
        ("enum-raw-bits", rt_option_float_pack(RuntimeValue::from_raw(0), 1, value)),
        ("enum-boxed-float", rt_option_float_pack(RuntimeValue::from_raw(0), 3, value)),
        ("none-enum", rt_option_float_pack(RuntimeValue::from_raw(0), 4, value)),
    ]
}

fn some_cases() -> Vec<(f64, &'static str)> {
    vec![
        (0.1, "Option::Some(0.1)"), // the bug report's value
        (1.0, "Option::Some(1.0)"), // raw bits alias TAG_INT: a type-erased sink cannot decode this
        (-0.0, "Option::Some(-0.0)"),
        (f64::from_bits(9221120237041090565), "Option::Some(NaN)"), // quiet NaN with low payload bits
    ]
}

#[test]
fn print_sink_renders_every_float_option_word_form_exactly() {
    for (value, expected) in some_cases() {
        for (form, word) in word_forms(value) {
            if form == "nil" || form == "none-enum" {
                continue;
            }
            assert_eq!(
                render(rt_opt_f64_to_string(word.to_raw() as i64)),
                expected,
                "rt_opt_f64_to_string({form} of {value})"
            );
        }
    }
    for (form, word) in word_forms(0.1) {
        if form == "nil" || form == "none-enum" {
            assert_eq!(
                render(rt_opt_f64_to_string(word.to_raw() as i64)),
                "Option::None",
                "rt_opt_f64_to_string({form})"
            );
        }
    }
}

#[test]
fn interpolation_sink_renders_every_float_option_word_form_exactly() {
    for (value, expected) in some_cases() {
        for (form, word) in word_forms(value) {
            // The tagged sink receives RuntimeValues: the flat RAW-bits word
            // is a raw-sink (rt_opt_f64_to_string) input only.
            if form == "nil" || form == "none-enum" || form == "flat-raw-bits" {
                continue;
            }
            assert_eq!(
                render(rt_opt_f64_value_to_string(word)),
                expected,
                "rt_opt_f64_value_to_string({form} of {value})"
            );
        }
    }
    for (form, word) in word_forms(0.1) {
        if form == "nil" || form == "none-enum" {
            assert_eq!(
                render(rt_opt_f64_value_to_string(word)),
                "Option::None",
                "rt_opt_f64_value_to_string({form})"
            );
        }
    }
}
