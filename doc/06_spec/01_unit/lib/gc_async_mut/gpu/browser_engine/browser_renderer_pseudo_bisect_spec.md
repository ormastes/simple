# Browser Renderer Pseudo Bisect Specification

> Tests covering pseudo-selector bisect.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Pseudo Bisect Specification

## Scenarios

### pseudo-selector bisect

#### not: applies when no option matches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- not: applies when no option matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("not: applies when no option matches")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_be_greater_than(0)
```

</details>

#### not: rejects when option matches

- not: rejects when option matches
   - Expected: _count_color(result.pixel_data, 0xFF0891B2u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("not: rejects when option matches")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.card, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_equal(0)
```

</details>

#### has-descendant: applies

- has-descendant: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has-descendant: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### has-direct-child: applies

- has-direct-child: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has-direct-child: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### has-direct-child: rejects nested descendant

- has-direct-child: rejects nested descendant
   - Expected: _count_color(result.pixel_data, 0xFF0E7490u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has-direct-child: rejects nested descendant")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><section><span class='badge'></span></section></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### first-child: applies

- first-child: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first-child: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### first-child: rejects later divs

- first-child: rejects later divs
   - Expected: _count_color(result.pixel_data, 0xFF1D4ED8u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first-child: rejects later divs")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### last-child: applies

- last-child: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last-child: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### last-child: rejects non-last

- last-child: rejects non-last
   - Expected: _count_color(result.pixel_data, 0xFFBE123Cu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last-child: rejects non-last")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_equal(0)
```

</details>

#### only-child: applies

- only-child: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("only-child: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_be_greater_than(0)
```

</details>

#### only-child: rejects when sibling exists

- only-child: rejects when sibling exists
   - Expected: _count_color(result.pixel_data, 0xFF9333EAu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("only-child: rejects when sibling exists")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_equal(0)
```

</details>

#### nth-child even: applies

- nth-child even: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nth-child even: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### nth-child odd: rejects even nodes

- nth-child odd: rejects even nodes
   - Expected: _count_color(result.pixel_data, 0xFF0E7490u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nth-child odd: rejects even nodes")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### empty: applies

- empty: applies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty: applies")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### empty: rejects when has content

- empty: rejects when has content
   - Expected: _count_color(result.pixel_data, 0xFF0F766Eu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty: rejects when has content")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div>content</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pseudo-selector bisect.
- pseudo-selector bisect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `5e83296a3a13b86c318b3850de573bfff0a457949d18ab477ddd569bb15e4db8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e83296a3a13b86c318b3850de573bfff0a457949d18ab477ddd569bb15e4db8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e83296a3a13b86c318b3850de573bfff0a457949d18ab477ddd569bb15e4db8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'not: applies when no option matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'not: rejects when option matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has-descendant: applies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
