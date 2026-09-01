# Skia Color Space Specification

> Tests for SkColorSpace named variants, transfer functions, chromaticity primaries, predicate helpers, and RGB→XYZ primary matrix stubs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Color Space Specification

Tests for SkColorSpace named variants, transfer functions, chromaticity primaries, predicate helpers, and RGB→XYZ primary matrix stubs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-010 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/color_space_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkColorSpace named variants, transfer functions, chromaticity primaries,
predicate helpers, and RGB→XYZ primary matrix stubs.

## Scenarios

### SkColorSpace named constructors

#### srgb() returns kind Srgb with Srgb transfer and D65 white point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- srgb() returns kind Srgb with Srgb transfer and D65 white point
   - Expected: cs.kind equals `SkColorSpaceKind.Srgb`
   - Expected: cs.transfer_fn equals `SkTransferFn.Srgb`
   - Expected: wx_ok is true
   - Expected: wy_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("srgb() returns kind Srgb with Srgb transfer and D65 white point")
val cs = srgb()
expect(cs.kind).to_equal(SkColorSpaceKind.Srgb)
expect(cs.transfer_fn).to_equal(SkTransferFn.Srgb)
val wx_ok = math_abs(cs.chromaticities.white_x - 0.3127) < 1e-5
expect(wx_ok).to_equal(true)
val wy_ok = math_abs(cs.chromaticities.white_y - 0.3290) < 1e-5
expect(wy_ok).to_equal(true)
```

</details>

#### display_p3() returns DisplayP3 kind with D65 white point

- display_p3() returns DisplayP3 kind with D65 white point
   - Expected: cs.kind equals `SkColorSpaceKind.DisplayP3`
   - Expected: wx_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("display_p3() returns DisplayP3 kind with D65 white point")
val cs = display_p3()
expect(cs.kind).to_equal(SkColorSpaceKind.DisplayP3)
val wx_ok = math_abs(cs.chromaticities.white_x - 0.3127) < 1e-5
expect(wx_ok).to_equal(true)
```

</details>

#### rec2020() returns Rec2020 kind with Pq transfer function

- rec2020() returns Rec2020 kind with Pq transfer function
   - Expected: cs.kind equals `SkColorSpaceKind.Rec2020`
   - Expected: cs.transfer_fn equals `SkTransferFn.Pq`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rec2020() returns Rec2020 kind with Pq transfer function")
val cs = rec2020()
expect(cs.kind).to_equal(SkColorSpaceKind.Rec2020)
expect(cs.transfer_fn).to_equal(SkTransferFn.Pq)
```

</details>

#### sk_color_space_is_srgb returns true for srgb()

- sk_color_space_is_srgb returns true for srgb()
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_color_space_is_srgb returns true for srgb()")
val cs = srgb()
val result = sk_color_space_is_srgb(cs)
expect(result).to_equal(true)
```

</details>

#### sk_color_space_is_wide_gamut returns true for display_p3()

- sk_color_space_is_wide_gamut returns true for display_p3()
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_color_space_is_wide_gamut returns true for display_p3()")
val cs = display_p3()
val result = sk_color_space_is_wide_gamut(cs)
expect(result).to_equal(true)
```

</details>

#### sk_color_space_is_wide_gamut returns false for srgb()

- sk_color_space_is_wide_gamut returns false for srgb()
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_color_space_is_wide_gamut returns false for srgb()")
val cs = srgb()
val result = sk_color_space_is_wide_gamut(cs)
expect(result).to_equal(false)
```

</details>

#### sk_color_space_is_hdr returns true for rec2020() which uses Pq transfer

- sk_color_space_is_hdr returns true for rec2020() which uses Pq transfer
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sk_color_space_is_hdr returns true for rec2020() which uses Pq transfer")
val cs = rec2020()
val result = sk_color_space_is_hdr(cs)
expect(result).to_equal(true)
```

</details>

<details>
<summary>Advanced: primary_matrix_for srgb has m00 ≈ 0.4124564</summary>

#### primary_matrix_for srgb has m00 ≈ 0.4124564

- primary_matrix_for srgb has m00 ≈ 0.4124564
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("primary_matrix_for srgb has m00 ≈ 0.4124564")
val cs = srgb()
val m = primary_matrix_for(cs)
val ok = math_abs(m.m00 - 0.4124564) < 1e-5
expect(ok).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c06df7d303aaba6eba0c65b9182881e4ef3a618341c3002eb4d5710d11b44f46`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c06df7d303aaba6eba0c65b9182881e4ef3a618341c3002eb4d5710d11b44f46`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c06df7d303aaba6eba0c65b9182881e4ef3a618341c3002eb4d5710d11b44f46`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/color_space_spec.spl
mirror: doc/06_spec/unit/lib/skia/color_space_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/color_space_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/color_space_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/color_space_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'srgb() returns kind Srgb with Srgb transfer and D65 white point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/color_space_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'display_p3() returns DisplayP3 kind with D65 white point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/color_space_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rec2020() returns Rec2020 kind with Pq transfer function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
