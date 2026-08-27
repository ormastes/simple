# Web Render Budget Default Arg Class Specification

> Tests covering an explicit i64 budget_ms does not poison paint across renderer entry points.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Budget Default Arg Class Specification

## Scenarios

### an explicit i64 budget_ms does not poison paint across renderer entry points

#### renders a non-blank scene through the plain entry point (positive control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a non-blank scene through the plain entry point (positive control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a non-blank scene through the plain entry point (positive control)")
# Guards a vacuous pass: if this goes blank the assertions below prove nothing.
val pixels = simple_web_layout_render_html_software_pixels(SCENE_HTML, W, H, BIG_BUDGET)
expect(_non_white(pixels) > 0).to_be_true()
```

</details>

#### software_pixels paints backgrounds when budget_ms is passed explicitly

- software_pixels paints backgrounds when budget_ms is passed explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software_pixels paints backgrounds when budget_ms is passed explicitly")
val explicit = simple_web_layout_render_html_software_pixels(SCENE_HTML, W, H, BIG_BUDGET)
expect(_non_white(explicit) > 0).to_be_true()
```

</details>

#### software_pixels_traced paints backgrounds when budget_ms is passed explicitly

- software_pixels_traced paints backgrounds when budget_ms is passed explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software_pixels_traced paints backgrounds when budget_ms is passed explicitly")
val explicit = simple_web_layout_render_html_software_pixels_traced(SCENE_HTML, W, H, BIG_BUDGET)
expect(_non_white(explicit) > 0).to_be_true()
```

</details>

#### software_pixels_at_scroll paints backgrounds when budget_ms is passed explicitly

- software_pixels_at_scroll paints backgrounds when budget_ms is passed explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software_pixels_at_scroll paints backgrounds when budget_ms is passed explicitly")
val explicit = simple_web_layout_render_html_software_pixels_at_scroll(SCENE_HTML, W, H, 0, BIG_BUDGET)
expect(_non_white(explicit) > 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering an explicit i64 budget_ms does not poison paint across renderer entry points.
- an explicit i64 budget_ms does not poison paint across renderer entry points

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

- Canonical SPipe generation for source `aec912f28922212cc698ae1b0b1318bdf64390bb53f2ad968cd1b94fd0c5baa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aec912f28922212cc698ae1b0b1318bdf64390bb53f2ad968cd1b94fd0c5baa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aec912f28922212cc698ae1b0b1318bdf64390bb53f2ad968cd1b94fd0c5baa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a non-blank scene through the plain entry point (positive control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software_pixels paints backgrounds when budget_ms is passed explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_render_budget_default_arg_class_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software_pixels_traced paints backgrounds when budget_ms is passed explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
