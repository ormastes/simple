# Browser Renderer Group31 50 Specification

> Tests covering group 31-50.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Group31 50 Specification

## Scenarios

### group 31-50

#### applies simple rules nested inside CSS layer blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies simple rules nested inside CSS layer blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple rules nested inside CSS layer blocks")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### applies functional selectors nested inside CSS layer blocks

- applies functional selectors nested inside CSS layer blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies functional selectors nested inside CSS layer blocks")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { div:not(.disabled) { width: 12px; height: 8px; background-color: #be123c; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### normalizes simple CSS nesting before fallback selector scans

- normalizes simple CSS nesting before fallback selector scans
   - Expected: normalized_document_style does not contain `&.primary`
   - Expected: normalized_html does not contain `&.primary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes simple CSS nesting before fallback selector scans")
val normalized = browser_renderer_normalize_style_rules(".card { width: 12px; height: 8px; &.primary { background-color: #7e22ce; } & span { color: #0f766e; } }")
val normalized_document_style = browser_renderer_normalize_style_rules("body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
val normalized_html = browser_renderer_normalize_style_blocks("<html><head><style>body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }</style></head><body><div class='card primary'></div></body></html>")
expect(normalized).to_contain(".card { width: 12px; height: 8px; }")
expect(normalized).to_contain(".card.primary { background-color: #7e22ce; }")
expect(normalized).to_contain(".card span { color: #0f766e; }")
expect(normalized_document_style).to_contain(".card.primary { width: 12px; height: 8px; background-color: #7e22ce; }")
expect(normalized_html).to_contain(".card.primary { width: 12px; height: 8px; background-color: #7e22ce; }")
expect(normalized_document_style.contains("&.primary")).to_equal(false)
expect(normalized_html.contains("&.primary")).to_equal(false)
```

</details>

#### applies simple CSS nesting with parent selector references

- applies simple CSS nesting with parent selector references


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple CSS nesting with parent selector references")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }</style></head><body><div class='card primary'></div></body></html>"
val flat_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #7e22ce; }</style></head><body><div class='card primary'></div></body></html>"
val normalized_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
val normalized_rule_html = "<html><head><style>" + normalized_css + "</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(normalized_rule_html, TEST_WIDTH, TEST_HEIGHT)
val flat_result = render_html_to_pixels_with_viewport(flat_html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(flat_result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
```

</details>

#### applies simple descendant rules from CSS nesting

- applies simple descendant rules from CSS nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple descendant rules from CSS nesting")
val red_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#dc2626; } }")
val green_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#16a34a; } }")
val red_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + red_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + green_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### applies attribute presence selectors

- applies attribute presence selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute presence selectors")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### applies exact attribute value selectors

- applies exact attribute value selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies exact attribute value selectors")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='active'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_be_greater_than(0)
```

</details>

#### rejects exact attribute value selectors with different values

- rejects exact attribute value selectors with different values
   - Expected: _count_color(result.pixel_data, 0xFF4D7C0Fu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects exact attribute value selectors with different values")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### applies attribute prefix selectors

- applies attribute prefix selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute prefix selectors")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F5E9Cu32)).to_be_greater_than(0)
```

</details>

#### rejects attribute suffix selectors without matching suffix

- rejects attribute suffix selectors without matching suffix
   - Expected: _count_color(result.pixel_data, 0xFF065F46u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects attribute suffix selectors without matching suffix")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF065F46u32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering group 31-50.
- group 31-50

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d72287c6c2ff69303aa5a78844a80ebc50cde93874b6f80436286b3b303c11a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d72287c6c2ff69303aa5a78844a80ebc50cde93874b6f80436286b3b303c11a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d72287c6c2ff69303aa5a78844a80ebc50cde93874b6f80436286b3b303c11a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies simple rules nested inside CSS layer blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies functional selectors nested inside CSS layer blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_group31_50_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes simple CSS nesting before fallback selector scans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
