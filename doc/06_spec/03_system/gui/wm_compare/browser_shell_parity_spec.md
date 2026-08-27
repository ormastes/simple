# Browser Shell Parity Specification

> Tests covering wm_compare framebuffer baseline/browser shell parity (browser-shell gate — simple_browser shell).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Shell Parity Specification

## Scenarios

### wm_compare framebuffer baseline/browser shell parity (browser-shell gate — simple_browser shell)

#### solid fill — BrowserCompositorBackend.clear() matches fb_driver

#### matches framebuffer exactly

- matches framebuffer exactly
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches framebuffer exactly")
val r = run_browser_shell_parity(scene_solid_fill())
expect(r.pass_exact).to_equal(true)
```

</details>

#### fill_rect row edge — exercises [x,x+w) half-open contract on browser shell

#### matches framebuffer exactly

- matches framebuffer exactly
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches framebuffer exactly")
val r = run_browser_shell_parity(scene_fill_rect_row_edge())
expect(r.pass_exact).to_equal(true)
```

</details>

#### text + bg — BrowserCompositorBackend.draw_char_8x16 bg cells

#### matches framebuffer exactly

- matches framebuffer exactly
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches framebuffer exactly")
val r = run_browser_shell_parity(scene_text_with_bg())
expect(r.pass_exact).to_equal(true)
```

</details>

#### glass blend — CompositorGlassCapable.blend_rect on browser shell

#### matches framebuffer exactly

- matches framebuffer exactly
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches framebuffer exactly")
val r = run_browser_shell_parity(scene_glass_blend())
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
val r = run_browser_shell_parity(scene_glass_blend())
expect(r.perceptual_diagnostic_only).to_equal(true)
expect(r.exact_required).to_equal(true)
expect(r.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### browser shell render harness self-check

#### returns a buffer of the expected length

- returns a buffer of the expected length
   - Expected: browser_pixels.len() equals `32 * 16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a buffer of the expected length")
val browser_pixels = render_browser_shell(scene_solid_fill())
expect(browser_pixels.len()).to_equal(32 * 16)
```

</details>

#### diffs identical browser shell buffers as exact

- diffs identical browser shell buffers as exact
   - Expected: r.pass_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diffs identical browser shell buffers as exact")
val a = render_browser_shell(scene_solid_fill())
val b = render_browser_shell(scene_solid_fill())
val r = diff_buffers("browser_shell_self_check", 32u32, 16u32, a, b)
expect(r.pass_exact).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/browser_shell_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare framebuffer baseline/browser shell parity (browser-shell gate — simple_browser shell).
- wm_compare framebuffer baseline/browser shell parity (browser-shell gate — simple_browser shell)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `36f00ab92b3da54812e4f492702a31499e1e1cec3f69712137d818f670c6b6f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36f00ab92b3da54812e4f492702a31499e1e1cec3f69712137d818f670c6b6f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36f00ab92b3da54812e4f492702a31499e1e1cec3f69712137d818f670c6b6f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/wm_compare/browser_shell_parity_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/browser_shell_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/browser_shell_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/browser_shell_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/browser_shell_parity_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches framebuffer exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/browser_shell_parity_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches framebuffer exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/browser_shell_parity_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches framebuffer exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
