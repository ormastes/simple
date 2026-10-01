# Simple Web Html Renderer Specification

> Tests covering SimpleWebHtmlRenderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Html Renderer Specification

## Scenarios

### SimpleWebHtmlRenderer

#### renders a white framebuffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a white framebuffer
   - Expected: pixels.len() equals `12`
   - Expected: pixels[0] equals `0xFFFFFFFFu32`
   - Expected: pixels[11] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a white framebuffer")
val pixels = simple_web_render_html_to_pixels("<html></html>", 4, 3)
expect(pixels.len()).to_equal(12)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixels[11]).to_equal(0xFFFFFFFFu32)
```

</details>

#### reuses retained pixels for unchanged html

- reuses retained pixels for unchanged html
   - Expected: first.len() equals `12`
   - Expected: second.len() equals `12`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses retained pixels for unchanged html")
var cache = SimpleWebHtmlPixelCache.create(4, 3)
val first = cache.pixels_for_html("<html></html>")
val second = cache.pixels_for_html("<html></html>")
expect(first.len()).to_equal(12)
expect(second.len()).to_equal(12)
expect(cache.stores).to_equal(1)
expect(cache.hits).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleWebHtmlRenderer.
- SimpleWebHtmlRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `adaeeaf01cbcf52e88108f4e75deec5755afd241ae34a8a0b44d6007da06c118`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `adaeeaf01cbcf52e88108f4e75deec5755afd241ae34a8a0b44d6007da06c118`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `adaeeaf01cbcf52e88108f4e75deec5755afd241ae34a8a0b44d6007da06c118`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a white framebuffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses retained pixels for unchanged html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
