//! Value creation, extraction, and type checking implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::tags;

#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}
/// Coerce a boxed RuntimeValue to a raw machine i64 with a full-width return.
/// Used by the InterpCall bridge to hand interpreter results back to compiled
/// code whose destination is a raw bool/int register (bool -> 0/1, nil -> 0).
///
/// A non-float heap value (array/text/tuple/struct/...) reaching here is
/// never legitimate: this path exists only for scalar/bool/handle
/// destinations, and every InterpCall whose declared return type is a heap
/// composite is supposed to be routed through `return_type_keeps_boxed` /
/// `interp_call_keeps_boxed_result` instead, which keeps the boxed
/// `RuntimeValue` intact rather than sending it here. When that
/// classification is wrong (as `Type::Array` was before this fix), the old
/// behavior below of falling through to `0` silently manufactured a
/// zero-length/zero-value result at exit 0 with no diagnostic -- exactly the
/// failure in
/// `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`
/// (`rt_tls13_sha256`'s `[u8]` digest unboxed here read back as length 0 for
/// every input). Fail loudly instead so a future boxed/unboxed
/// classification gap is caught immediately rather than shipping a silent
/// wrong answer.
#[no_mangle]
pub extern "C" fn rt_value_raw_i64(v: RuntimeValue) -> i64 {
    if v.is_int() {
        v.as_int()
    } else if v.is_bool() {
        i64::from(v.as_bool())
    } else if v.is_float() {
        v.as_float() as i64
    } else if v.is_heap() {
        panic!(
            "rt_value_raw_i64: refusing to truncate a non-float heap-boxed InterpCall \
             result (tag={}) to a raw i64 -- this result should have stayed boxed \
             (see compilability.rs::return_type_keeps_boxed / \
             codegen::instr::core::interp_call_keeps_boxed_result); truncating it here \
             would silently manufacture a zero-length/zero-value result. See \
             doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md",
            v.tag()
        );
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}
#[no_mangle]
pub extern "C" fn rt_value_type_tag(v: RuntimeValue) -> u8 {
    v.tag() as u8
}
#[no_mangle]
pub extern "C" fn rt_is_error(v: RuntimeValue) -> bool {
    v.tag() == tags::TAG_SPECIAL && v.payload() == tags::SPECIAL_ERROR
}

#[cfg(test)]
mod raw_i64_guard_tests {
    use super::*;

    /// Env var flag used by `heap_array_panics_instead_of_silently_truncating`
    /// below to re-exec the test binary as a subprocess. `rt_value_raw_i64`
    /// is `extern "C"`, so a panic inside it aborts the process rather than
    /// unwinding (unwinding across a non-Rust-ABI boundary is UB) -- that
    /// abort can't be caught with `#[should_panic]` in-process, so this test
    /// drives it out-of-process and asserts on the exit status instead.
    const SUBPROCESS_ENV: &str = "RT_VALUE_RAW_I64_GUARD_SUBPROCESS_CHILD";

    #[test]
    fn scalar_kinds_still_unbox_normally() {
        if std::env::var_os(SUBPROCESS_ENV).is_some() {
            return; // Only the panic child below cares about this env var.
        }
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_int(42)), 42);
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_bool(true)), 1);
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_bool(false)), 0);
        assert_eq!(rt_value_raw_i64(RuntimeValue::NIL), 0);
    }

    /// Regression guard for
    /// `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`:
    /// a non-float heap-boxed InterpCall result (array/text/tuple) reaching
    /// this unbox path used to silently fall through to `0`, which is exactly
    /// how `rt_tls13_sha256`'s `[u8]` digest read back as length 0 under the
    /// Cranelift JIT for every input, at exit 0, with no diagnostic. This
    /// path must now fail loudly (process abort with a diagnostic message)
    /// instead of manufacturing a silent wrong answer.
    #[test]
    fn heap_array_panics_instead_of_silently_truncating() {
        if std::env::var_os(SUBPROCESS_ENV).is_some() {
            // Child mode: actually trigger the guard. The parent asserts on
            // how this process dies, so nothing after this line should run.
            let arr = crate::value::collections::rt_byte_array_new_len(4);
            assert!(arr.is_heap(), "test fixture must produce a heap value");
            let _ = rt_value_raw_i64(arr);
            panic!("rt_value_raw_i64 returned instead of aborting on a heap array");
        }

        let exe = std::env::current_exe().expect("current_exe");
        let output = std::process::Command::new(exe)
            .arg("heap_array_panics_instead_of_silently_truncating")
            .arg("--nocapture")
            .env(SUBPROCESS_ENV, "1")
            .output()
            .expect("spawn subprocess child");

        assert!(
            !output.status.success(),
            "child process must NOT exit successfully when unboxing a heap array; \
             a clean exit here means the silent-truncation regression is back"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("refusing to truncate a non-float heap-boxed"),
            "expected the loud rt_value_raw_i64 guard message on stderr, got: {stderr}"
        );
    }
}
