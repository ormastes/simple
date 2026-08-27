# Browser Renderer Nesting Bisect Specification

> Tests covering CSS nesting bisect.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Nesting Bisect Specification

## Scenarios

### CSS nesting bisect

#### flat card.primary selector renders color

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flat card.primary selector renders color


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flat card.primary selector renders color")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #7e22ce; }</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
```

</details>

#### normalizes &.primary to .card.primary

- normalizes &.primary to .card.primary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes &.primary to .card.primary")
val normalized = browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
expect(normalized).to_contain(".card.primary {")
```

</details>

#### normalized CSS renders card.primary color

- normalized CSS renders card.primary color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalized CSS renders card.primary color")
val css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
val html = "<html><head><style>" + css + "</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
```

</details>

#### layer blocks: simple class selector inside layer

- layer blocks: simple class selector inside layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layer blocks: simple class selector inside layer")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### layer blocks: :not() inside layer applies when no option matches

- layer blocks: :not() inside layer applies when no option matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layer blocks: :not() inside layer applies when no option matches")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { div:not(.disabled) { width: 12px; height: 8px; background-color: #be123c; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### descendant span text color red vs green

- descendant span text color red vs green


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("descendant span text color red vs green")
val red_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#dc2626; } }")
val green_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#16a34a; } }")
val red_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + red_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + green_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSS nesting bisect.
- CSS nesting bisect

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `331feda7782bbcf5b803ed7a120f4086a001e63a081388eb28e6b0f2e8c51fad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `331feda7782bbcf5b803ed7a120f4086a001e63a081388eb28e6b0f2e8c51fad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `331feda7782bbcf5b803ed7a120f4086a001e63a081388eb28e6b0f2e8c51fad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flat card.primary selector renders color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes &.primary to .card.primary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_nesting_bisect_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalized CSS renders card.primary color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
