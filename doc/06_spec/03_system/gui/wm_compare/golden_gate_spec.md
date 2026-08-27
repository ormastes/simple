# Golden Gate Specification

> Tests covering wm_compare golden-image gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Golden Gate Specification

## Scenarios

### wm_compare golden-image gate

#### solid_fill golden

#### loads from disk

- loads from disk
   - Expected: r.loaded_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads from disk")
val r = check_golden(scene_solid_fill())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### matches the golden exactly

- matches the golden exactly
   - Expected: r.pass_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches the golden exactly")
val r = check_golden(scene_solid_fill())
expect(r.pass_gate).to_equal(true)
```

</details>

#### fill_rect_row_edge golden

#### loads from disk

- loads from disk
   - Expected: r.loaded_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads from disk")
val r = check_golden(scene_fill_rect_row_edge())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

- stays within drift budget
   - Expected: r.pass_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stays within drift budget")
val r = check_golden(scene_fill_rect_row_edge())
expect(r.pass_gate).to_equal(true)
```

</details>

#### text_with_bg golden

#### loads from disk

- loads from disk
   - Expected: r.loaded_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads from disk")
val r = check_golden(scene_text_with_bg())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

- stays within drift budget
   - Expected: r.pass_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stays within drift budget")
val r = check_golden(scene_text_with_bg())
expect(r.pass_gate).to_equal(true)
```

</details>

#### glass_blend golden

#### loads from disk

- loads from disk
   - Expected: r.loaded_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads from disk")
val r = check_golden(scene_glass_blend())
expect(r.loaded_ok).to_equal(true)
```

</details>

#### stays within drift budget

- stays within drift budget
   - Expected: r.pass_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stays within drift budget")
val r = check_golden(scene_glass_blend())
expect(r.pass_gate).to_equal(true)
```

</details>

#### PPM encoder/decoder roundtrip

#### round-trips a freshly rendered scene exactly

- round-trips a freshly rendered scene exactly
   - Expected: decoded.len() equals `pixels.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips a freshly rendered scene exactly")
val pixels = render_framebuffer_baseline(scene_solid_fill())
val bytes = encode_ppm_p6(32u32, 16u32, pixels)
val decoded = decode_ppm_p6(bytes)
expect(decoded.len()).to_equal(pixels.len())
```

</details>

#### writes a P6 magic header

- writes a P6 magic header
   - Expected: bytes[0] equals `80u8`
   - Expected: bytes[1] equals `54u8`
   - Expected: bytes[2] equals `10u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes a P6 magic header")
val pixels = render_framebuffer_baseline(scene_solid_fill())
val bytes = encode_ppm_p6(32u32, 16u32, pixels)
# 'P' = 80, '6' = 54, '\n' = 10
expect(bytes[0]).to_equal(80u8)
expect(bytes[1]).to_equal(54u8)
expect(bytes[2]).to_equal(10u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/golden_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare golden-image gate.
- wm_compare golden-image gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d8e10b5ff0e1f5822e476aa00194aaef9a742250b97b73f4641e57448d637d4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8e10b5ff0e1f5822e476aa00194aaef9a742250b97b73f4641e57448d637d4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8e10b5ff0e1f5822e476aa00194aaef9a742250b97b73f4641e57448d637d4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/golden_gate_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/golden_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/golden_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/golden_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/golden_gate_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads from disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/golden_gate_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the golden exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/golden_gate_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads from disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
