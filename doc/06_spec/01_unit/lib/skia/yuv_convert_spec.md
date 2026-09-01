# Skia YUV Convert Specification

> Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia YUV Convert Specification

Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-012 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/yuv_convert_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color
conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

## Scenarios

### yuv_convert

#### yuv_to_rgb: BT.601 full-range pure-gray Y=0.5, U=0.5, V=0.5 -> RGB=(0.5, 0.5, 0.5)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- yuv_to_rgb: BT.601 full-range pure-gray Y=0.5, U=0.5, V=0.5 -> RGB=(0.5, 0.5, 0.5)
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yuv_to_rgb: BT.601 full-range pure-gray Y=0.5, U=0.5, V=0.5 -> RGB=(0.5, 0.5, 0.5)")
val rgb = yuv_to_rgb(0.5, 0.5, 0.5, YuvMatrix.BT601, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 0.5) < 1e-6
val g_ok = math_abs(g - 0.5) < 1e-6
val b_ok = math_abs(b - 0.5) < 1e-6
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### yuv_to_rgb: BT.709 pure red round-trips via rgb_to_yuv

- yuv_to_rgb: BT.709 pure red round-trips via rgb_to_yuv
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yuv_to_rgb: BT.709 pure red round-trips via rgb_to_yuv")
val yuv = rgb_to_yuv(1.0, 0.0, 0.0, YuvMatrix.BT709, YuvRange.Full)
val y = yuv.0
val u = yuv.1
val v = yuv.2
val rgb = yuv_to_rgb(y, u, v, YuvMatrix.BT709, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 1.0) < 1e-3
val g_ok = math_abs(g - 0.0) < 1e-3
val b_ok = math_abs(b - 0.0) < 1e-3
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### rgb_to_yuv -> yuv_to_rgb round-trip preserves RGB within 1e-3

- rgb_to_yuv -> yuv_to_rgb round-trip preserves RGB within 1e-3
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rgb_to_yuv -> yuv_to_rgb round-trip preserves RGB within 1e-3")
val yuv = rgb_to_yuv(0.3, 0.6, 0.2, YuvMatrix.BT601, YuvRange.Full)
val y = yuv.0
val u = yuv.1
val v = yuv.2
val rgb = yuv_to_rgb(y, u, v, YuvMatrix.BT601, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 0.3) < 1e-3
val g_ok = math_abs(g - 0.6) < 1e-3
val b_ok = math_abs(b - 0.2) < 1e-3
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### yuv_to_rgb: output clamps to [0, 1] -- extreme inputs don't overshoot

- yuv_to_rgb: output clamps to [0, 1] -- extreme inputs don't overshoot


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yuv_to_rgb: output clamps to [0, 1] -- extreme inputs don't overshoot")
# Extreme UV should push channels outside [0,1] before clamping.
val rgb_high = yuv_to_rgb(1.0, 1.0, 1.0, YuvMatrix.BT601, YuvRange.Full)
val rgb_low  = yuv_to_rgb(0.0, 0.0, 0.0, YuvMatrix.BT601, YuvRange.Full)
expect(rgb_high.0).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.1).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.2).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.0).to_be_greater_than(0.0 - 1e-9)
expect(rgb_high.1).to_be_greater_than(0.0 - 1e-9)
expect(rgb_high.2).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.0).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.1).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.2).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.0).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.1).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.2).to_be_greater_than(0.0 - 1e-9)
```

</details>

#### yuv_bitmap_to_rgba: dimension mismatch returns empty bitmap

- yuv_bitmap_to_rgba: dimension mismatch returns empty bitmap
   - Expected: out.width equals `0`
   - Expected: out.height equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yuv_bitmap_to_rgba: dimension mismatch returns empty bitmap")
val yp = Bitmap.zeros(4, 4)
val up = Bitmap.zeros(4, 4)
val vp = Bitmap.zeros(3, 4)
val out = yuv_bitmap_to_rgba(yp, up, vp, YuvMatrix.BT601, YuvRange.Full)
expect(out.width).to_equal(0)
expect(out.height).to_equal(0)
```

</details>

#### yuv_bitmap_to_rgba: uniform Y=U=V=0.5 input produces roughly uniform gray output

- yuv_bitmap_to_rgba: uniform Y=U=V=0.5 input produces roughly uniform gray output
   - Expected: out.width equals `w`
   - Expected: out.height equals `h`
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a0 equals `255 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yuv_bitmap_to_rgba: uniform Y=U=V=0.5 input produces roughly uniform gray output")
val w = 2
val h = 2
val yp = Bitmap.zeros(w, h)
val up = Bitmap.zeros(w, h)
val vp = Bitmap.zeros(w, h)
# Fill each plane's channel 0 with 128 (~0.5)
var py = 0
while py < h:
    var px = 0
    while px < w:
        val gray = SkColor4f(r: 0.5, g: 0.0, b: 0.0, a: 0.0)
        yp.set_pixel(px, py, gray)
        up.set_pixel(px, py, gray)
        vp.set_pixel(px, py, gray)
        px = px + 1
    py = py + 1
val out = yuv_bitmap_to_rgba(yp, up, vp, YuvMatrix.BT601, YuvRange.Full)
expect(out.width).to_equal(w)
expect(out.height).to_equal(h)
# Sample (0,0) -- expect R,G,B all near 0.5 (which is ~128/255)
val r0 = out.pixels[0]
val g0 = out.pixels[1]
val b0 = out.pixels[2]
val a0 = out.pixels[3]
val r_ok = math_abs((r0 as f64) - 128.0) < 4.0
val g_ok = math_abs((g0 as f64) - 128.0) < 4.0
val b_ok = math_abs((b0 as f64) - 128.0) < 4.0
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a0).to_equal(255 as u8)
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

- Canonical SPipe generation for source `805c8c833c227bf272eb81a551e5b95757883000ed9e1055e9dca88c07cd722e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `805c8c833c227bf272eb81a551e5b95757883000ed9e1055e9dca88c07cd722e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `805c8c833c227bf272eb81a551e5b95757883000ed9e1055e9dca88c07cd722e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/skia/yuv_convert_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/yuv_convert_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/yuv_convert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/yuv_convert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/yuv_convert_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/yuv_convert_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yuv_to_rgb: BT.601 full-range pure-gray Y=0.5, U=0.5, V=0.5 -> RGB=(0.5, 0.5, 0.5)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/yuv_convert_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yuv_to_rgb: BT.709 pure red round-trips via rgb_to_yuv' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/yuv_convert_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rgb_to_yuv -> yuv_to_rgb round-trip preserves RGB within 1e-3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
