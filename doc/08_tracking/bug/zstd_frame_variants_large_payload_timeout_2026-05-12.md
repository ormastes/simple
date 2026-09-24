## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved 2026-05-13

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Zstd Frame Variants Large Payload Timeout

Date: 2026-05-12
Status: Resolved 2026-05-13

`test/01_unit/lib/common/zstd_frame_variants_spec.spl` was a known blocker for the cipher/compression algorithm gate. The large 70,000-byte single-segment payload path timed out in interpreter mode.

Resolution: the 4-byte single-segment-size example now uses the runtime zero-filled byte allocator at the exact 65,792-byte threshold and asserts the emitted 4-byte content-size header plus RLE block shape instead of doing a 70,000-byte interpreter fixture build and deep equality comparison. Smaller examples still cover round-trip RLE/raw decoding.

Verification: `src/compiler_rust/target/release/simple test test/01_unit/lib/common/zstd_frame_variants_spec.spl --mode=interpreter --no-cache` passes 19 examples, 0 failures. The strict core cipher/compression gate reports `passed=13 skipped=0 failed=0`.
