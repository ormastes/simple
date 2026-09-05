# Browser Renderer Flat Selector Specification

> Tests covering flat selector regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Flat Selector Specification

## Scenarios

### flat selector regression

#### flat .card.primary selector works

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flat .card.primary selector works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flat .card.primary selector works")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #7e22ce; }</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
```

</details>

#### normalize produces card.primary

- normalize produces card.primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalize produces card.primary")
val normalized = browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
expect(normalized).to_contain(".card.primary {")
```

</details>

#### normalized CSS has card.primary rule

- normalized CSS has card.primary rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalized CSS has card.primary rule")
val css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
expect(css).to_contain(".card.primary {")
expect(css).to_contain("background-color: #7e22ce")
```

</details>

#### layer: .card inside @layer works

- layer: .card inside @layer works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layer: .card inside @layer works")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flat selector regression.
- flat selector regression

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

- Canonical SPipe generation for source `8a5178ab80c7ed2f2c88ddb784e0522f05f22aa54ed1f03502d4e35df7454ff7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a5178ab80c7ed2f2c88ddb784e0522f05f22aa54ed1f03502d4e35df7454ff7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a5178ab80c7ed2f2c88ddb784e0522f05f22aa54ed1f03502d4e35df7454ff7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flat .card.primary selector works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalize produces card.primary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_flat_selector_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalized CSS has card.primary rule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
