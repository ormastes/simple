use super::*;

fn text(value: &str) -> RuntimeValue {
    unsafe { rt_string_new(value.as_ptr(), value.len() as u64) }
}

fn text_bytes(value: RuntimeValue) -> Vec<u8> {
    unsafe { std::slice::from_raw_parts(rt_string_data(value), rt_string_len(value) as usize).to_vec() }
}

#[test]
fn signed_add_retains_full_width_and_wraps() {
    for (left, right, expected) in [
        (5, 3, 8),
        ((1i64 << 60) - 1, 1, 1i64 << 60),
        (i64::MAX, 1, i64::MIN),
        (i64::MIN, -1, i64::MAX),
        (i64::MIN, i64::MAX, -1),
    ] {
        assert_eq!(rt_tagged_add(RuntimeValue::from_int(left), RuntimeValue::from_int(right)).as_int(), expected);
    }
    // Keep the existing Rust tagged rt_any_add behavior separately intact.
    assert_eq!(rt_any_add(RuntimeValue::from_int(5), RuntimeValue::from_int(3)).as_int(), 8);
}

#[test]
fn float_and_mixed_add_preserve_registered_numeric_values() {
    for (left, right, expected) in [
        (RuntimeValue::from_float(2.5), RuntimeValue::from_float(0.5), 3.0),
        (RuntimeValue::from_float(2.5), RuntimeValue::from_int(3), 5.5),
        (RuntimeValue::from_int(3), RuntimeValue::from_float(2.5), 5.5),
        (RuntimeValue::from_float(f64::from_bits(0x3ff0000000000001)), RuntimeValue::from_float(0.0), f64::from_bits(0x3ff0000000000001)),
    ] {
        let result = rt_tagged_add(left, right);
        assert!(result.is_float());
        assert_eq!(result.as_float().to_bits(), f64::to_bits(expected));
    }
}

#[test]
fn registered_text_coerces_wide_signed_unsigned_float_and_nil() {
    for (value, expected) in [
        (RuntimeValue::from_int(1i64 << 60), "n=1152921504606846976"),
        (RuntimeValue::from_int(i64::MIN), "n=-9223372036854775808"),
        (RuntimeValue::from_u64(u64::MAX), "n=18446744073709551615"),
        (RuntimeValue::from_float(2.5), "n=2.5"),
        (RuntimeValue::NIL, "n="),
    ] {
        assert_eq!(text_bytes(rt_tagged_add(text("n="), value)), expected.as_bytes());
    }
}

#[test]
fn invalid_numeric_operands_use_exact_failure_protocol() {
    let executable = std::env::current_exe().unwrap();
    for mode in ["nil", "uint", "unregistered"] {
        let output = std::process::Command::new(&executable)
            .args(["--exact", "value::collections::tagged_add_tests::negative_child", "--nocapture"])
            .env("SIMPLE_TAGGED_ADD_NEGATIVE", mode)
            .output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert_eq!(String::from_utf8(output.stderr).unwrap(),
            "panic: rt_tagged_add: operands require signed integer, float or text\n");
    }
}

#[test]
fn negative_child() {
    let Ok(mode) = std::env::var("SIMPLE_TAGGED_ADD_NEGATIVE") else { return; };
    let value = match mode.as_str() {
        "nil" => RuntimeValue::NIL,
        "uint" => RuntimeValue::from_u64(u64::MAX),
        // tags.rs: TAG_INT=0 and TAG_HEAP=1; 4096 is aligned/unregistered.
        "unregistered" => RuntimeValue::from_raw(4096 | 1),
        _ => panic!("unexpected negative mode"),
    };
    rt_tagged_add(value, RuntimeValue::from_int(1));
    panic!("negative numeric operand returned");
}
