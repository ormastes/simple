# Simd Native Rows Specification

> Tests covering simd_native_rows — fill_row_u32 / fill_buffer_u32 / fill_rows_u32 parity, simd_native_rows — copy_row_u32 / blend family parity, simd_native_rows — native_hits accounting (real, verified per-function).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Native Rows Specification

## Scenarios

### simd_native_rows — fill_row_u32 / fill_buffer_u32 / fill_rows_u32 parity

#### fill_row_u32 matches oracle_fill_const per element

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fill_row_u32 matches oracle_fill_const per element


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_row_u32 matches oracle_fill_const per element")
val n: i64 = 64
val native = engine2d_simd_fill_row_u32(n, 0xFF224466)
var oracle_buf: [u32] = [0; 64]
oracle_fill_const(oracle_buf, 0, n, 0xFF224466)
assert_true(oracle_hash_span(oracle_buf, 0, n) == oracle_hash_span(native, 0, n))
assert_true(native.len() == 64)
assert_true(native[0] == 0xFF224466)
```

</details>

#### fill_buffer_u32 mirrors fill_row_u32 for positive count and returns empty for count<=0

- fill_buffer_u32 mirrors fill_row_u32 for positive count and returns empty for count<=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_buffer_u32 mirrors fill_row_u32 for positive count and returns empty for count<=0")
val n: i64 = 32
val native = engine2d_simd_fill_buffer_u32(n, 0x11223344)
var oracle_buf: [u32] = [0; 32]
oracle_fill_const(oracle_buf, 0, n, 0x11223344)
assert_true(oracle_hash_span(oracle_buf, 0, n) == oracle_hash_span(native, 0, n))
assert_true(engine2d_simd_fill_buffer_u32(0, 0xFFFFFFFF).len() == 0)
assert_true(engine2d_simd_fill_buffer_u32(-1, 0xFFFFFFFF).len() == 0)
```

</details>

#### fill_rows_u32 fills width*height pixels and returns empty for non-positive dims

- fill_rows_u32 fills width*height pixels and returns empty for non-positive dims


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_rows_u32 fills width*height pixels and returns empty for non-positive dims")
val rows = engine2d_simd_fill_rows_u32(8, 4, 0xAABBCCDD, 1)
var oracle_buf: [u32] = [0; 32]
oracle_fill_const(oracle_buf, 0, 32, 0xAABBCCDD)
assert_true(rows.len() == 32)
assert_true(oracle_hash_span(oracle_buf, 0, 32) == oracle_hash_span(rows, 0, 32))
assert_true(engine2d_simd_fill_rows_u32(0, 4, 0xFFFFFFFF, 1).len() == 0)
assert_true(engine2d_simd_fill_rows_u32(4, 0, 0xFFFFFFFF, 1).len() == 0)
assert_true(engine2d_simd_fill_rows_u32(-1, 4, 0xFFFFFFFF, 1).len() == 0)
```

</details>

### simd_native_rows — copy_row_u32 / blend family parity

#### copy_row_u32 reproduces src content bit-exact

- copy_row_u32 reproduces src content bit-exact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copy_row_u32 reproduces src content bit-exact")
val src = filled_random(64, 42)
val cp = engine2d_simd_copy_row_u32(src)
assert_true(cp.len() == 64)
assert_true(oracle_hash_span(cp, 0, 64) == oracle_hash_span(src, 0, 64))
```

</details>

#### blend_row_u32 matches oracle_src_over_image (pinned via oracle hash)

- blend_row_u32 matches oracle_src_over_image (pinned via oracle hash)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_row_u32 matches oracle_src_over_image (pinned via oracle hash)")
var dst_row = filled_random(64, 7)
var src_row = filled_random(64, 8)
val blended = engine2d_simd_blend_row_u32(dst_row, src_row)
var oracle_dst = filled_random(64, 7)
var oracle_src = filled_random(64, 8)
oracle_src_over_image(oracle_dst, 0, oracle_src, 0, 64)
assert_true(oracle_hash_span(blended, 0, 64) == oracle_hash_span(oracle_dst, 0, 64))
```

</details>

#### blend_span_u32 matches oracle_src_over_image (pinned hash)

- blend_span_u32 matches oracle_src_over_image (pinned hash)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span_u32 matches oracle_src_over_image (pinned hash)")
var dst = filled_random(64, 100)
var src = filled_random(64, 101)
val blended = engine2d_simd_blend_span_u32(dst, 0, src, 0, 64)
var oracle_dst = filled_random(64, 100)
var oracle_src = filled_random(64, 101)
oracle_src_over_image(oracle_dst, 0, oracle_src, 0, 64)
assert_true(oracle_hash_span(blended, 0, 64) == oracle_hash_span(oracle_dst, 0, 64))
```

</details>

#### blend_const_span_u32 matches oracle_src_over_const

- blend_const_span_u32 matches oracle_src_over_const


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span_u32 matches oracle_src_over_const")
var dst = filled_random(64, 200)
val blended = engine2d_simd_blend_const_span_u32(dst, 0, 64, 0x80FF2244)
var oracle_dst = filled_random(64, 200)
oracle_src_over_const(oracle_dst, 0, 64, 0x80FF2244)
assert_true(oracle_hash_span(blended, 0, 64) == oracle_hash_span(oracle_dst, 0, 64))
```

</details>

#### blend_const_span_u32 with sa==0 constant colour is a no-op, matching the oracle

- blend_const_span_u32 with sa==0 constant colour is a no-op, matching the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span_u32 with sa==0 constant colour is a no-op, matching the oracle")
var dst = filled_random(64, 201)
val blended = engine2d_simd_blend_const_span_u32(dst, 0, 64, 0x00FF2244)
var oracle_dst = filled_random(64, 201)
oracle_src_over_const(oracle_dst, 0, 64, 0x00FF2244)
assert_true(oracle_hash_span(blended, 0, 64) == oracle_hash_span(oracle_dst, 0, 64))
```

</details>

### simd_native_rows — native_hits accounting (real, verified per-function)

#### native_hits increments exactly once for a fill_row_u32 call at/above the SIMD threshold, and reset zeroes it

- native_hits increments exactly once for a fill_row_u32 call at/above the SIMD threshold, and reset zeroes it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native_hits increments exactly once for a fill_row_u32 call at/above the SIMD threshold, and reset zeroes it")
engine2d_simd_native_reset()
assert_true(engine2d_simd_native_hits() == 0)
engine2d_simd_fill_row_u32(64, 0xFF000000)
assert_true(engine2d_simd_native_hits() == 1)
engine2d_simd_native_reset()
assert_true(engine2d_simd_native_hits() == 0)
```

</details>

#### native_hits increments exactly once for a copy_row_u32 call at/above the SIMD threshold

- native_hits increments exactly once for a copy_row_u32 call at/above the SIMD threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native_hits increments exactly once for a copy_row_u32 call at/above the SIMD threshold")
engine2d_simd_native_reset()
engine2d_simd_copy_row_u32(filled_random(64, 5))
assert_true(engine2d_simd_native_hits() == 1)
engine2d_simd_native_reset()
```

</details>

#### a below-threshold fill_row_u32 call (count<4) falls back to scalar and does not record a SIMD hit, but is still correct

- a below-threshold fill_row_u32 call (count<4) falls back to scalar and does not record a SIMD hit, but is still correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a below-threshold fill_row_u32 call (count<4) falls back to scalar and does not record a SIMD hit, but is still correct")
engine2d_simd_native_reset()
val small = engine2d_simd_fill_row_u32(2, 0xFF000000)
assert_true(engine2d_simd_native_hits() == 0)
assert_true(small.len() == 2)
assert_true(small[0] == 0xFF000000)
assert_true(small[1] == 0xFF000000)
engine2d_simd_native_reset()
```

</details>

#### blend_row_u32/blend_span_u32/blend_const_span_u32 never record a native_hits SIMD row hit (Rust bridge computes blends inline, not via the row-hit-counted fill/copy path)

- blend_row_u32/blend_span_u32/blend_const_span_u32 never record a native_hits SIMD row hit (Rust bridge computes blends inline, not via the row-hit-counted fill/copy path)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_row_u32/blend_span_u32/blend_const_span_u32 never record a native_hits SIMD row hit (Rust bridge computes blends inline, not via the row-hit-counted fill/copy path)")
engine2d_simd_native_reset()
engine2d_simd_blend_row_u32(filled_random(64, 1), filled_random(64, 2))
assert_true(engine2d_simd_native_hits() == 0)
engine2d_simd_blend_span_u32(filled_random(64, 3), 0, filled_random(64, 4), 0, 64)
assert_true(engine2d_simd_native_hits() == 0)
engine2d_simd_blend_const_span_u32(filled_random(64, 6), 0, 64, 0x80FF2244)
assert_true(engine2d_simd_native_hits() == 0)
engine2d_simd_native_reset()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simd_native_rows — fill_row_u32 / fill_buffer_u32 / fill_rows_u32 parity, simd_native_rows — copy_row_u32 / blend family parity, simd_native_rows — native_hits accounting (real, verified per-function).
- simd_native_rows — fill_row_u32 / fill_buffer_u32 / fill_rows_u32 parity
- simd_native_rows — copy_row_u32 / blend family parity
- simd_native_rows — native_hits accounting (real, verified per-function)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3936d31e678978464cb61f872522399a48019c3d871f44163d6c7c29f92617fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3936d31e678978464cb61f872522399a48019c3d871f44163d6c7c29f92617fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3936d31e678978464cb61f872522399a48019c3d871f44163d6c7c29f92617fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_row_u32 matches oracle_fill_const per element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_buffer_u32 mirrors fill_row_u32 for positive count and returns empty for count<=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_rows_u32 fills width*height pixels and returns empty for non-positive dims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
