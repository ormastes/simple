# Browser Renderer Smoke Specification

> Tests covering BrowserRenderer bounded smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Smoke Specification

## Scenarios

### BrowserRenderer bounded smoke

#### renders inline background blocks without producing a blank frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders inline background blocks without producing a blank frame
   - Expected: pixels.len() equals `SMOKE_WIDTH * SMOKE_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders inline background blocks without producing a blank frame")
val html = "<html><body><div style='width: 120px; height: 60px; background-color: #ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(pixels.len()).to_equal(SMOKE_WIDTH * SMOKE_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders style block CSS into fallback pixels

- renders style block CSS into fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders style block CSS into fallback pixels")
val html = "<html><head><style>body { margin: 0; } .card { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(_count_color(pixels, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### is deterministic for repeated renders of the same HTML

- is deterministic for repeated renders of the same HTML
   - Expected: _pixels_equal(first, second) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic for repeated renders of the same HTML")
val html = "<html><body style='margin:0; background:#ffffff'><div style='width:10px; height:10px; background:#16a34a'></div></body></html>"
val first = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
val second = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(_pixels_equal(first, second)).to_equal(true)
```

</details>

#### keeps explicit Engine2D software rendering available

- keeps explicit Engine2D software rendering available
   - Expected: result.width equals `SMOKE_WIDTH`
   - Expected: result.height equals `SMOKE_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps explicit Engine2D software rendering available")
val renderer = create_software_browser_renderer(SMOKE_WIDTH, SMOKE_HEIGHT)
val result = renderer.render_html("<html><body><div style='width:10px; height:10px; background:#dc2626'></div></body></html>")
expect(result.width).to_equal(SMOKE_WIDTH)
expect(result.height).to_equal(SMOKE_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer bounded smoke.
- BrowserRenderer bounded smoke

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

- Canonical SPipe generation for source `edb25884d2886613aec7a17f003a69b0d0c9c4629b614022d95e5eb9ff8afdfa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edb25884d2886613aec7a17f003a69b0d0c9c4629b614022d95e5eb9ff8afdfa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edb25884d2886613aec7a17f003a69b0d0c9c4629b614022d95e5eb9ff8afdfa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders inline background blocks without producing a blank frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders style block CSS into fallback pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is deterministic for repeated renders of the same HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
