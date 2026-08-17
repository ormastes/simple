//! Regression + class-detection tests for the 61-bit boxed-int channel.
//!
//! Bug: `doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
//! `RuntimeValue::from_int` stored integers as `(v << 3) | TAG_INT`, leaving a
//! 61-bit SIGNED payload. Out-of-range values came back silently wrong, never
//! with an error: `0x8010000000000000` lost bit 63, `2^62` came back `0`, and
//! `i64::MAX` came back `-1`. The fix heap-boxes anything that does not
//! round-trip inline; it landed with no test at all, which is what these cover.

use simple_runtime::value::RuntimeValue;

/// Reproducing test: the exact values named in the bug report.
#[test]
fn wide_ints_from_the_bug_report_roundtrip() {
    for &v in &[
        0x8010_0000_0000_0000u64 as i64, // the reported value; bit 63 was dropped
        1i64 << 62,                      // came back 0
        i64::MAX,                        // came back -1
        i64::MIN,
    ] {
        assert_eq!(
            RuntimeValue::from_int(v).as_int(),
            v,
            "from_int({v:#x}).as_int() must round-trip, not truncate to 61 bits"
        );
        // Non-vacuity: spell out what the pre-fix encoding produced and assert
        // `from_int` is NOT doing that. Without this, deleting the range check
        // in `from_int` could in principle be masked by some future reader that
        // happens to agree with the truncation on both sides.
        let pre_fix = ((v as u64).wrapping_shl(3) as i64) >> 3;
        assert_ne!(
            pre_fix, v,
            "test fixture is wrong: {v:#x} is not actually out of inline range"
        );
    }
}

/// Class-detection test: generalizes past the reported values to the whole
/// defect class -- *any* i64 that does not fit the inline payload. Scans both
/// sides of the 2^60 boundary plus a spread of full-width bit patterns, so a
/// future change that re-narrows the channel (or gets the boundary off by one)
/// fails here even if the four reported constants happen to survive.
#[test]
fn every_i64_survives_the_inline_boundary() {
    let mut cases: Vec<i64> = Vec::new();

    // Every power-of-two magnitude and its neighbours, both signs. This walks
    // straight across the 2^60 inline/heap boundary in both directions.
    for bit in 0..63 {
        let p = 1i64 << bit;
        for delta in [-1i64, 0, 1] {
            cases.push(p.wrapping_add(delta));
            cases.push(p.wrapping_neg().wrapping_add(delta));
        }
    }
    // All-ones and alternating patterns: these have set bits above bit 60, so
    // an untagging `>> 3` mangles them in a way single-bit cases can miss.
    cases.extend_from_slice(&[
        i64::MAX,
        i64::MIN,
        -1,
        0,
        0x5555_5555_5555_5555u64 as i64,
        0xAAAA_AAAA_AAAA_AAAAu64 as i64,
        0x7FFF_FFFF_FFFF_FFFFu64 as i64,
        0x8000_0000_0000_0001u64 as i64,
    ]);

    for v in cases {
        let boxed = RuntimeValue::from_int(v);
        assert_eq!(
            boxed.as_int(),
            v,
            "from_int({v:#x}) lost bits: got {:#x}",
            boxed.as_int()
        );
        // A wide value must actually take the heap path -- if it claims to be
        // an inline int while holding an out-of-range payload, some *other*
        // reader that untags directly will still see the truncated value.
        assert_eq!(
            RuntimeValue::fits_inline_int(v),
            boxed.is_int(),
            "{v:#x}: fits_inline_int disagrees with the representation actually chosen"
        );
    }
}

/// The predicate itself must agree with what the inline encoding can hold.
/// Written independently of `fits_inline_int`'s own range constants so a typo
/// in those constants cannot make this test agree with the bug.
#[test]
fn fits_inline_int_matches_the_actual_inline_capacity() {
    for bit in 0..63 {
        for v in [1i64 << bit, -(1i64 << bit)] {
            // What the raw inline encoding would do, computed with wrapping
            // arithmetic so the overflow is observed rather than panicking.
            let roundtripped = ((v as u64).wrapping_shl(3) as i64) >> 3;
            assert_eq!(
                RuntimeValue::fits_inline_int(v),
                roundtripped == v,
                "fits_inline_int({v:#x}) is wrong about the inline encoding"
            );
        }
    }
}
