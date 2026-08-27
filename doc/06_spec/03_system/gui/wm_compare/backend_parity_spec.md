# Backend Parity Specification

> Tests covering wm_compare framebuffer/software parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Parity Specification

## Scenarios

### wm_compare framebuffer/software parity

#### solid fill — clear() on both backends

#### produces zero per-channel delta

- produces zero per-channel delta
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces zero per-channel delta")
val r = run_framebuffer_software_parity(scene_solid_fill())
expect(r.pass_exact).to_equal(true)
```

</details>

#### marks perceptual as diagnostic only

- marks perceptual as diagnostic only
   - Expected: r.perceptual_diagnostic_only is true
   - Expected: r.exact_required is true
   - Expected: r.tolerance_acceptance_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks perceptual as diagnostic only")
val r = run_framebuffer_software_parity(scene_solid_fill())
expect(r.perceptual_diagnostic_only).to_equal(true)
expect(r.exact_required).to_equal(true)
expect(r.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### fill_rect on the row edge — exercises [x,x+w) half-open contract

#### row 0 + row h-1 fill_rect matches framebuffer↔software

- row 0 + row h-1 fill_rect matches framebuffer↔software
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("row 0 + row h-1 fill_rect matches framebuffer↔software")
val r = run_framebuffer_software_parity(scene_fill_rect_row_edge())
expect(r.pass_exact).to_equal(true)
```

</details>

#### differs in zero pixels

- differs in zero pixels
   - Expected: r.differing_pixels equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("differs in zero pixels")
val r = run_framebuffer_software_parity(scene_fill_rect_row_edge())
expect(r.differing_pixels).to_equal(0u32)
```

</details>

#### text+bg — draw_text background cells match between backends

#### max channel delta on bg cells is 0

- max channel delta on bg cells is 0
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("max channel delta on bg cells is 0")
val r = run_framebuffer_software_parity(scene_text_with_bg())
# software reference flat-block glyph stub matches framebuffer baseline bg writes; this
# validates the bg-cell contract, NOT the glyph rasterizer.
expect(r.pass_exact).to_equal(true)
```

</details>

#### glass blend — degraded blend_rect math

#### exact-match blend output

- exact-match blend output
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exact-match blend output")
val r = run_framebuffer_software_parity(scene_glass_blend())
expect(r.pass_exact).to_equal(true)
```

</details>

#### requires exact pixels for blend output acceptance

- requires exact pixels for blend output acceptance
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exact pixels for blend output acceptance")
val r = run_framebuffer_software_parity(scene_glass_blend())
expect(r.pass_exact).to_equal(true)
```

</details>

#### diff harness self-check

#### reports identical buffers as exact

- reports identical buffers as exact
   - Expected: r.max_channel_delta equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports identical buffers as exact")
val baseline = render_framebuffer_baseline(scene_solid_fill())
val reference = render_software_reference(scene_solid_fill())
val r = diff_buffers("self_check", 32u32, 16u32, baseline, reference)
expect(r.max_channel_delta).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/backend_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare framebuffer/software parity.
- wm_compare framebuffer/software parity

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8b3e01a27102a13521aae298f18c0afa2daf8a9bc562bb117a7bff4fc5640d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8b3e01a27102a13521aae298f18c0afa2daf8a9bc562bb117a7bff4fc5640d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8b3e01a27102a13521aae298f18c0afa2daf8a9bc562bb117a7bff4fc5640d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/backend_parity_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/backend_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/backend_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/backend_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/backend_parity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces zero per-channel delta' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/backend_parity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks perceptual as diagnostic only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/backend_parity_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'row 0 + row h-1 fill_rect matches framebuffer↔software' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
