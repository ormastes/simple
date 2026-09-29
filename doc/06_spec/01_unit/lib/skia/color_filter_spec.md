# Skia Color Filter Specification

> Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity, Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap) dispatch paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Color Filter Specification

Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity, Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap) dispatch paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-COLORFILTER |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/color_filter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity,
Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both
scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap)
dispatch paths.

## Scenarios

### color_filter

#### apply_color_filter_to_pixel: Identity returns input unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- apply_color_filter_to_pixel: Identity returns input unchanged
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_pixel: Identity returns input unchanged")
val f = color_filter_identity()
val out = apply_color_filter_to_pixel(0.25, 0.5, 0.75, 0.8, f)
val r_ok = math_abs(out.0 - 0.25) < 1e-9
val g_ok = math_abs(out.1 - 0.5) < 1e-9
val b_ok = math_abs(out.2 - 0.75) < 1e-9
val a_ok = math_abs(out.3 - 0.8) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_pixel: Invert turns (1,0,0,1) into (0,1,1,1)

- apply_color_filter_to_pixel: Invert turns (1,0,0,1) into (0,1,1,1)
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_pixel: Invert turns (1,0,0,1) into (0,1,1,1)")
val f = color_filter_invert()
val out = apply_color_filter_to_pixel(1.0, 0.0, 0.0, 1.0, f)
val r_ok = math_abs(out.0 - 0.0) < 1e-9
val g_ok = math_abs(out.1 - 1.0) < 1e-9
val b_ok = math_abs(out.2 - 1.0) < 1e-9
val a_ok = math_abs(out.3 - 1.0) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_pixel: Grayscale of pure red gives l ~ 0.299

- apply_color_filter_to_pixel: Grayscale of pure red gives l ~ 0.299
   - Expected: l_close is true
   - Expected: gb_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_pixel: Grayscale of pure red gives l ~ 0.299")
val f = color_filter_grayscale()
val out = apply_color_filter_to_pixel(1.0, 0.0, 0.0, 1.0, f)
val l = out.0
val l_close = math_abs(l - 0.299) < 1e-9
expect(l_close).to_equal(true)
# R == G == B for grayscale output
val gb_match = math_abs(out.1 - l) < 1e-12 and math_abs(out.2 - l) < 1e-12
expect(gb_match).to_equal(true)
expect(l).to_be_greater_than(0.0)
expect(l).to_be_less_than(1.0)
```

</details>

<details>
<summary>Advanced: apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged</summary>

#### apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged

- apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged")
val id_m = [1.0, 0.0, 0.0, 0.0, 0.0,
            0.0, 1.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 1.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0, 0.0]
val f = color_filter_matrix(id_m)
val out = apply_color_filter_to_pixel(0.2, 0.4, 0.6, 0.9, f)
val r_ok = math_abs(out.0 - 0.2) < 1e-9
val g_ok = math_abs(out.1 - 0.4) < 1e-9
val b_ok = math_abs(out.2 - 0.6) < 1e-9
val a_ok = math_abs(out.3 - 0.9) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>


</details>

#### apply_color_filter_to_pixel: Grayscale preserves alpha

- apply_color_filter_to_pixel: Grayscale preserves alpha
   - Expected: a_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_pixel: Grayscale preserves alpha")
val f = color_filter_grayscale()
val alpha_in = 0.42
val out = apply_color_filter_to_pixel(0.8, 0.3, 0.1, alpha_in, f)
val a_ok = math_abs(out.3 - alpha_in) < 1e-12
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_bitmap: Invert on a 2x2 bitmap returns inverted pixels

- apply_color_filter_to_bitmap: Invert on a 2x2 bitmap returns inverted pixels
   - Expected: out.width equals `2`
   - Expected: out.height equals `2`
   - Expected: out.pixels[0] equals `0 as u8`
   - Expected: out.pixels[1] equals `255 as u8`
   - Expected: out.pixels[2] equals `255 as u8`
   - Expected: out.pixels[3] equals `255 as u8`
   - Expected: out.pixels[4] equals `255 as u8`
   - Expected: out.pixels[5] equals `0 as u8`
   - Expected: out.pixels[6] equals `255 as u8`
   - Expected: out.pixels[7] equals `255 as u8`
   - Expected: out.pixels[8] equals `255 as u8`
   - Expected: out.pixels[9] equals `255 as u8`
   - Expected: out.pixels[10] equals `0 as u8`
   - Expected: out.pixels[11] equals `255 as u8`
   - Expected: out.pixels[12] equals `0 as u8`
   - Expected: out.pixels[13] equals `0 as u8`
   - Expected: out.pixels[14] equals `0 as u8`
   - Expected: out.pixels[15] equals `255 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("apply_color_filter_to_bitmap: Invert on a 2x2 bitmap returns inverted pixels")
val bmp = Bitmap.zeros(2, 2)
# pixel (0,0) = red, fully opaque
bmp.set_pixel(0, 0, sk_color4f(1.0, 0.0, 0.0, 1.0))
# pixel (1,0) = green, fully opaque
bmp.set_pixel(1, 0, sk_color4f(0.0, 1.0, 0.0, 1.0))
# pixel (0,1) = blue, fully opaque
bmp.set_pixel(0, 1, sk_color4f(0.0, 0.0, 1.0, 1.0))
# pixel (1,1) = white, fully opaque
bmp.set_pixel(1, 1, sk_color4f(1.0, 1.0, 1.0, 1.0))
val f = color_filter_invert()
val out = apply_color_filter_to_bitmap(bmp, f)
expect(out.width).to_equal(2)
expect(out.height).to_equal(2)
# Red (255,0,0,255) -> (0,255,255,255)
expect(out.pixels[0]).to_equal(0 as u8)
expect(out.pixels[1]).to_equal(255 as u8)
expect(out.pixels[2]).to_equal(255 as u8)
expect(out.pixels[3]).to_equal(255 as u8)
# Green (0,255,0,255) -> (255,0,255,255)
expect(out.pixels[4]).to_equal(255 as u8)
expect(out.pixels[5]).to_equal(0 as u8)
expect(out.pixels[6]).to_equal(255 as u8)
expect(out.pixels[7]).to_equal(255 as u8)
# Blue (0,0,255,255) -> (255,255,0,255)
expect(out.pixels[8]).to_equal(255 as u8)
expect(out.pixels[9]).to_equal(255 as u8)
expect(out.pixels[10]).to_equal(0 as u8)
expect(out.pixels[11]).to_equal(255 as u8)
# White (255,255,255,255) -> (0,0,0,255)
expect(out.pixels[12]).to_equal(0 as u8)
expect(out.pixels[13]).to_equal(0 as u8)
expect(out.pixels[14]).to_equal(0 as u8)
expect(out.pixels[15]).to_equal(255 as u8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3e7821346cdf5538a113ffe9c50aa5d920db8c471c5ca3735443895bfc109e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e7821346cdf5538a113ffe9c50aa5d920db8c471c5ca3735443895bfc109e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e7821346cdf5538a113ffe9c50aa5d920db8c471c5ca3735443895bfc109e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/skia/color_filter_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/color_filter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/color_filter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/color_filter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/color_filter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/color_filter_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_color_filter_to_pixel: Identity returns input unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/color_filter_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_color_filter_to_pixel: Invert turns (1,0,0,1) into (0,1,1,1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/color_filter_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_color_filter_to_pixel: Grayscale of pure red gives l ~ 0.299' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
