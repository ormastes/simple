# Tmp 57to62 Specification

> Tests covering BrowserRenderer HTML rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp 57to62 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### applies tag id compound selectors over bare id selectors in fallback pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies tag id compound selectors over bare id selectors in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag id compound selectors over bare id selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div#hero { width: 12px; height: 8px; background-color: #dc2626; } #hero { background-color: #2563eb; }</style></head><body><div id='hero'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### renders simple nested span text in fallback pixels

- renders simple nested span text in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders simple nested span text in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #fef3c7; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
expect(_count_non_background(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
```

</details>

#### uses nested span style when rendering fallback text pixels

- uses nested span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses nested span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#dc2626'>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#16a34a'>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor descendant span style when rendering fallback text pixels

- uses ancestor descendant span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor descendant span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor id descendant span style when rendering fallback text pixels

- uses ancestor id descendant span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor id descendant span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#dc2626; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#16a34a; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor child span style when rendering fallback text pixels

- uses ancestor child span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor child span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer HTML rendering.
- BrowserRenderer HTML rendering

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab92d8674e473d94313348606c9fdad73d7ccc473b2fcbf5cff40f2e5dd5731d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab92d8674e473d94313348606c9fdad73d7ccc473b2fcbf5cff40f2e5dd5731d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab92d8674e473d94313348606c9fdad73d7ccc473b2fcbf5cff40f2e5dd5731d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies tag id compound selectors over bare id selectors in fallback pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders simple nested span text in fallback pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_57to62_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses nested span style when rendering fallback text pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
