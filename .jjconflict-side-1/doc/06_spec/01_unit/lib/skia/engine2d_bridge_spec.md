# Engine2d Bridge Specification

> Tests covering SkiaEngine2DBridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Bridge Specification

## Scenarios

### SkiaEngine2DBridge

#### replays skia rect ops onto the shared Engine2D cpu_simd backend lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replays skia rect ops onto the shared Engine2D cpu_simd backend lane
   - Expected: pixels.len() equals `w * h`
   - Expected: inside equals `0xFFEF4444u32`
   - Expected: outside equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays skia rect ops onto the shared Engine2D cpu_simd backend lane")
val w = 24
val h = 16
val bg = sk_color_argb(255, 0x12, 0x34, 0x56)   # 0xFF123456
val fg = sk_color_argb(255, 0xEF, 0x44, 0x44)   # 0xFFEF4444
val pic = _record_two_rects(w, h, bg, fg)
val pixels = skia_render_picture_on_engine2d(pic, w, h, "cpu_simd")

# Buffer is the right size.
expect(pixels.len()).to_equal(w * h)

# A pixel INSIDE the fg rect (8,5) == the fg paint color.
val inside = pixels[8 + 5 * w]
expect(inside).to_equal(0xFFEF4444u32)

# A pixel OUTSIDE the fg rect (20,14) == the background color.
val outside = pixels[20 + 14 * w]
expect(outside).to_equal(0xFF123456u32)
```

</details>

#### replays the same picture on the software backend lane

- replays the same picture on the software backend lane
   - Expected: pixels.len() equals `w * h`
   - Expected: pixels[8 + 5 * w] equals `0xFFEF4444u32`
   - Expected: pixels[20 + 14 * w] equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays the same picture on the software backend lane")
val w = 24
val h = 16
val bg = sk_color_argb(255, 0x12, 0x34, 0x56)
val fg = sk_color_argb(255, 0xEF, 0x44, 0x44)
val pic = _record_two_rects(w, h, bg, fg)
val pixels = skia_render_picture_on_engine2d(pic, w, h, "software")

expect(pixels.len()).to_equal(w * h)
expect(pixels[8 + 5 * w]).to_equal(0xFFEF4444u32)
expect(pixels[20 + 14 * w]).to_equal(0xFF123456u32)
```

</details>

#### reports both fill rects as mapped with nothing skipped

- reports both fill rects as mapped with nothing skipped
   - Expected: result.report.mapped_rects equals `2`
   - Expected: result.report.skipped equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports both fill rects as mapped with nothing skipped")
val w = 24
val h = 16
val bg = sk_color_argb(255, 0x12, 0x34, 0x56)
val fg = sk_color_argb(255, 0xEF, 0x44, 0x44)
val pic = _record_two_rects(w, h, bg, fg)
val result = skia_render_picture_on_engine2d_reported(pic, w, h, "cpu_simd")

expect(result.report.mapped_rects).to_equal(2)
expect(result.report.skipped).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/engine2d_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SkiaEngine2DBridge.
- SkiaEngine2DBridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `db5ae9b5e3e4655f2f62ecce487a60834f009498c804e238a43f0cb7e4f34c5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db5ae9b5e3e4655f2f62ecce487a60834f009498c804e238a43f0cb7e4f34c5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db5ae9b5e3e4655f2f62ecce487a60834f009498c804e238a43f0cb7e4f34c5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/skia/engine2d_bridge_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/engine2d_bridge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/engine2d_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/engine2d_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/engine2d_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/engine2d_bridge_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays skia rect ops onto the shared Engine2D cpu_simd backend lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/engine2d_bridge_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays the same picture on the software backend lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/engine2d_bridge_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports both fill rects as mapped with nothing skipped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
