# Web Render Explicit Budget Arg Specification

> Tests covering software-pixel renderer explicit i64 budget argument.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Explicit Budget Arg Specification

## Scenarios

### software-pixel renderer explicit i64 budget argument

#### loads the browser_engine module graph without a trim recursion overflow

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the browser_engine module graph without a trim recursion overflow
   - Expected: pixels.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the browser_engine module graph without a trim recursion overflow")
# Reaching this line at all means the module graph loaded; the reported
# overflow happened during module-graph preprocessing, before user code.
val pixels = simple_web_layout_render_html_software_pixels(RED_BOX_HTML, W, H)
expect(pixels.len()).to_equal(W * H)
```

</details>

#### paints background rectangles when budget_ms is omitted

- paints background rectangles when budget_ms is omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints background rectangles when budget_ms is omitted")
val pixels = simple_web_layout_render_html_software_pixels(RED_BOX_HTML, W, H)
expect(_count_color(pixels, RED) > 0).to_be_true()
```

</details>

#### paints the same background rectangles when budget_ms is passed explicitly

- paints the same background rectangles when budget_ms is passed explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints the same background rectangles when budget_ms is passed explicitly")
val pixels = simple_web_layout_render_html_software_pixels(RED_BOX_HTML, W, H, 30000)
expect(_count_color(pixels, RED) > 0).to_be_true()
```

</details>

#### produces an identical expected-color pixel count for default and explicit budget

- produces an identical expected-color pixel count for default and explicit budget
   - Expected: _count_color(explicit, RED) equals `_count_color(defaulted, RED)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces an identical expected-color pixel count for default and explicit budget")
val defaulted = simple_web_layout_render_html_software_pixels(RED_BOX_HTML, W, H)
val explicit = simple_web_layout_render_html_software_pixels(RED_BOX_HTML, W, H, 30000)
expect(_count_color(explicit, RED)).to_equal(_count_color(defaulted, RED))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering software-pixel renderer explicit i64 budget argument.
- software-pixel renderer explicit i64 budget argument

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `4b2b4cc219070521ccd26752b7ce2c6008ea76dad0ea5c71b45bd4d54a491178`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b2b4cc219070521ccd26752b7ce2c6008ea76dad0ea5c71b45bd4d54a491178`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b2b4cc219070521ccd26752b7ce2c6008ea76dad0ea5c71b45bd4d54a491178`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the browser_engine module graph without a trim recursion overflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints background rectangles when budget_ms is omitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_explicit_budget_arg_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints the same background rectangles when budget_ms is passed explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
