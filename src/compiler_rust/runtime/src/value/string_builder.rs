//! Incremental string builder runtime primitives.
//!
//! Building a large string via the `acc = acc + piece` pattern calls
//! [`rt_string_concat`](super::collections::rt_string_concat) once per piece,
//! and each call allocates a fresh buffer of size `len(acc) + len(piece)` and
//! copies all prior content. For `k` pieces totalling `N` bytes this is
//! `O(N^2)` copy work (see bug `rt_string_concat_quadratic_2026-06-12`).
//!
//! These externs back an amortized-`O(1)` push using a heap [`String`] (which
//! grows its capacity exponentially), turning the whole accumulation into
//! `O(N)`.
//!
//! ## Handle representation
//!
//! Following the opaque-handle convention used by `gemm_runtime`
//! (`Box::into_raw(...) as i64` validated by a magic tag), a builder handle is
//! a `Box<RuntimeStringBuilder>` raw pointer widened to `i64`. The first field
//! is a magic constant so a malformed / stale / zero handle is rejected rather
//! than dereferenced. `0` is the canonical null/invalid handle.
//!
//! ## Lifecycle (no GC)
//!
//! This runtime has no garbage collector. A builder is a transient owner, so
//! it follows the explicit-free convention of `gemm_runtime` rather than the
//! allocate-and-leak convention of interned `rt_string_*` values:
//!
//! * [`rt_string_builder_finish`] consumes the handle: it reclaims the `Box`,
//!   copies the accumulated bytes out into a normal runtime string, and drops
//!   the builder. The normal "build then finish" path therefore does **not**
//!   leak.
//! * [`rt_string_builder_free`] is provided for the abandon path (a builder
//!   created but never finished).
//!
//! Caveat: a builder that is `new`'d and then neither `finish`ed nor `free`d
//! leaks its backing `String` — there is no GC to reclaim it. Callers (and the
//! `StringBuilder` stdlib wrapper) must always end with `finish()` or `free()`.

use super::collections::{rt_string_data, rt_string_len, rt_string_new};
use super::core::RuntimeValue;

const STRING_BUILDER_MAGIC: u64 = 0x5342_5544_5F31_3233; // "SBUD_123"

#[repr(C)]
pub struct RuntimeStringBuilder {
    magic: u64,
    buf: String,
}

/// Validate a raw handle and return a mutable reference to the builder.
///
/// Returns `None` for the null handle (`0`) or any pointer whose magic tag
/// does not match (stale / corrupt / wrong-type handle).
unsafe fn builder_from_handle(handle: i64) -> Option<&'static mut RuntimeStringBuilder> {
    if handle == 0 {
        return None;
    }
    let b = &mut *(handle as *mut RuntimeStringBuilder);
    if b.magic != STRING_BUILDER_MAGIC {
        return None;
    }
    Some(b)
}

/// Create a new empty string builder.
///
/// Returns an opaque `i64` handle, or `0` on allocation failure. The handle
/// must eventually be passed to [`rt_string_builder_finish`] (which consumes
/// it) or [`rt_string_builder_free`]; otherwise the backing buffer leaks.
#[no_mangle]
pub extern "C" fn rt_string_builder_new() -> i64 {
    Box::into_raw(Box::new(RuntimeStringBuilder {
        magic: STRING_BUILDER_MAGIC,
        buf: String::new(),
    })) as i64
}

/// Append a runtime string `s` to the builder identified by `handle`.
///
/// Amortized `O(len(s))` — the backing `String` grows its capacity
/// exponentially. No-op if the handle is invalid or `s` is not a string.
/// Returns `1` on success, `0` on failure.
///
/// # Safety
/// `handle` must be a live handle previously returned by
/// [`rt_string_builder_new`] (and not yet finished/freed).
#[no_mangle]
pub unsafe extern "C" fn rt_string_builder_push(handle: i64, s: RuntimeValue) -> i64 {
    let Some(builder) = builder_from_handle(handle) else {
        return 0;
    };
    let len = rt_string_len(s);
    if len < 0 {
        return 0;
    }
    if len == 0 {
        return 1;
    }
    let data = rt_string_data(s);
    if data.is_null() {
        return 0;
    }
    let bytes = std::slice::from_raw_parts(data, len as usize);
    // Runtime strings are UTF-8; preserve bytes exactly without re-validating.
    match std::str::from_utf8(bytes) {
        Ok(text) => builder.buf.push_str(text),
        Err(_) => {
            // Defensive: append raw bytes even if not valid UTF-8 so no data is
            // silently dropped. Safe because we immediately reconstruct a
            // String from the same bytes on the same Vec.
            let v = std::mem::take(&mut builder.buf).into_bytes();
            let mut v = v;
            v.extend_from_slice(bytes);
            builder.buf = String::from_utf8_unchecked(v);
        }
    }
    1
}

/// Finish the builder: consume the handle, return the accumulated bytes as a
/// normal runtime string, and drop the builder (no leak).
///
/// After this call `handle` is dangling and must not be reused. Returns
/// `RuntimeValue::NIL` for an invalid handle.
///
/// # Safety
/// `handle` must be a live handle previously returned by
/// [`rt_string_builder_new`] and not already finished/freed.
#[no_mangle]
pub unsafe extern "C" fn rt_string_builder_finish(handle: i64) -> RuntimeValue {
    if builder_from_handle(handle).is_none() {
        return RuntimeValue::NIL;
    }
    // Reclaim ownership and drop the builder once we have copied its bytes out.
    let boxed = Box::from_raw(handle as *mut RuntimeStringBuilder);
    let bytes = boxed.buf.as_bytes();
    rt_string_new(bytes.as_ptr(), bytes.len() as u64)
}

/// Current accumulated byte length of the builder, or `-1` if invalid.
///
/// Does not consume the handle. Useful for tests/diagnostics.
///
/// # Safety
/// `handle` must be a live handle from [`rt_string_builder_new`].
#[no_mangle]
pub unsafe extern "C" fn rt_string_builder_len(handle: i64) -> i64 {
    match builder_from_handle(handle) {
        Some(b) => b.buf.len() as i64,
        None => -1,
    }
}

/// Free a builder without producing a string (abandon path).
///
/// No-op for an invalid handle. After this call `handle` is dangling.
///
/// # Safety
/// `handle` must be a live handle from [`rt_string_builder_new`] and not
/// already finished/freed.
#[no_mangle]
pub unsafe extern "C" fn rt_string_builder_free(handle: i64) {
    if builder_from_handle(handle).is_none() {
        return;
    }
    drop(Box::from_raw(handle as *mut RuntimeStringBuilder));
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    /// Read a runtime string value back into a Rust `String` for assertions.
    unsafe fn rv_to_string(v: RuntimeValue) -> String {
        let len = rt_string_len(v);
        assert!(len >= 0, "expected a string runtime value");
        if len == 0 {
            return String::new();
        }
        let data = rt_string_data(v);
        assert!(!data.is_null());
        let bytes = std::slice::from_raw_parts(data, len as usize);
        std::str::from_utf8(bytes).unwrap().to_string()
    }

    unsafe fn rt_str(s: &str) -> RuntimeValue {
        rt_string_new(s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn empty_builder_finishes_to_empty_string() {
        unsafe {
            let h = rt_string_builder_new();
            assert!(h != 0);
            let out = rt_string_builder_finish(h);
            assert_eq!(rv_to_string(out), "");
        }
    }

    #[test]
    fn push_accumulates_in_order() {
        unsafe {
            let h = rt_string_builder_new();
            assert_eq!(rt_string_builder_push(h, rt_str("hello")), 1);
            assert_eq!(rt_string_builder_push(h, rt_str(", ")), 1);
            assert_eq!(rt_string_builder_push(h, rt_str("world")), 1);
            assert_eq!(rt_string_builder_len(h), 12);
            let out = rt_string_builder_finish(h);
            assert_eq!(rv_to_string(out), "hello, world");
        }
    }

    #[test]
    fn empty_push_is_noop_but_succeeds() {
        unsafe {
            let h = rt_string_builder_new();
            assert_eq!(rt_string_builder_push(h, rt_str("")), 1);
            assert_eq!(rt_string_builder_push(h, rt_str("x")), 1);
            assert_eq!(rt_string_builder_push(h, rt_str("")), 1);
            let out = rt_string_builder_finish(h);
            assert_eq!(rv_to_string(out), "x");
        }
    }

    #[test]
    fn invalid_handle_is_rejected_safely() {
        unsafe {
            assert_eq!(rt_string_builder_len(0), -1);
            assert_eq!(rt_string_builder_push(0, rt_str("x")), 0);
            let out = rt_string_builder_finish(0);
            assert_eq!(rt_string_len(out), -1); // NIL is not a string
            rt_string_builder_free(0); // must not crash
        }
    }

    #[test]
    fn free_abandons_without_string() {
        unsafe {
            let h = rt_string_builder_new();
            rt_string_builder_push(h, rt_str("discarded"));
            rt_string_builder_free(h); // no leak, no string produced
        }
    }

    /// The builder result must match naive `acc = acc + piece` byte-for-byte.
    #[test]
    fn matches_naive_concatenation() {
        let cases: &[&[&str]] = &[
            &["a", "b", "c"],
            &["", "x", "", "y", ""],
            &["foo", "bar", "baz", "qux"],
            &["unicode: ", "\u{1F600}", " mixed ", "\u{00e9}\u{4e2d}"],
            &["{\"key\":", "\"value\"", ",", "\"n\":", "42", "}"],
        ];
        for case in cases {
            let naive: String = case.iter().copied().collect();
            unsafe {
                let h = rt_string_builder_new();
                for piece in *case {
                    assert_eq!(rt_string_builder_push(h, rt_str(piece)), 1);
                }
                let out = rt_string_builder_finish(h);
                assert_eq!(rv_to_string(out), naive, "case {:?}", case);
            }
        }
    }

    /// Builds a large string from many small pieces; verifies the full content.
    #[test]
    fn large_build_is_correct() {
        const N: usize = 10_000;
        let piece = "abcdefghij"; // 10 bytes
        unsafe {
            let h = rt_string_builder_new();
            for _ in 0..N {
                assert_eq!(rt_string_builder_push(h, rt_str(piece)), 1);
            }
            let out = rt_string_builder_finish(h);
            let s = rv_to_string(out);
            assert_eq!(s.len(), N * piece.len());
            // Spot-check structure: it is exactly N copies of `piece`.
            let expected: String = std::iter::repeat(piece).take(N).collect();
            assert_eq!(s, expected);
        }
    }

    /// Demonstrates the O(n) win: the builder pushes N pieces in roughly linear
    /// time, while naive `acc = acc + piece` (simulated with `rt_string_concat`)
    /// for the same N is visibly slower (quadratic). Timing is printed so the
    /// orchestrator can see the scaling. Not a hard threshold assertion beyond a
    /// generous ceiling, to avoid CI flakiness on shared/loaded machines.
    #[test]
    fn builder_scales_linearly_vs_quadratic_naive() {
        use super::super::collections::rt_string_concat;

        let piece_s = "x".repeat(8);
        let n_big: usize = 100_000;

        // Builder path: push N pieces.
        let t0 = Instant::now();
        let builder_out = unsafe {
            let h = rt_string_builder_new();
            for _ in 0..n_big {
                rt_string_builder_push(h, rt_str(&piece_s));
            }
            rt_string_builder_finish(h)
        };
        let builder_dt = t0.elapsed();
        let builder_len = unsafe { rt_string_len(builder_out) };
        assert_eq!(builder_len as usize, n_big * piece_s.len());

        // Naive path: acc = acc + piece, but only for a much SMALLER N, because
        // it is quadratic and 100k would take far too long. We measure a size
        // where it is already visibly slower than the builder for the same n.
        let n_small: usize = 20_000;
        let t1 = Instant::now();
        unsafe {
            let mut acc = rt_str("");
            for _ in 0..n_small {
                acc = rt_string_concat(acc, rt_str(&piece_s));
            }
            assert_eq!(rt_string_len(acc) as usize, n_small * piece_s.len());
        }
        let naive_dt = t1.elapsed();

        // Builder path for the SAME smaller N, for an apples-to-apples ratio.
        let t2 = Instant::now();
        unsafe {
            let h = rt_string_builder_new();
            for _ in 0..n_small {
                rt_string_builder_push(h, rt_str(&piece_s));
            }
            rt_string_builder_free(h);
        }
        let builder_small_dt = t2.elapsed();

        println!(
            "[string_builder perf] builder N={} took {:?}; \
             naive concat N={} took {:?}; builder N={} took {:?} \
             (naive/builder ratio at N={} = {:.1}x)",
            n_big,
            builder_dt,
            n_small,
            naive_dt,
            n_small,
            builder_small_dt,
            n_small,
            naive_dt.as_secs_f64() / builder_small_dt.as_secs_f64().max(1e-9),
        );

        // Generous ceiling: building 100k pieces should be well under a second.
        assert!(
            builder_dt.as_secs_f64() < 1.0,
            "builder should be near-linear; took {:?} for N={}",
            builder_dt,
            n_big
        );
        // At equal N, the builder must beat naive quadratic concat.
        assert!(
            builder_small_dt < naive_dt,
            "builder ({:?}) should beat naive concat ({:?}) at N={}",
            builder_small_dt,
            naive_dt,
            n_small
        );
    }
}
