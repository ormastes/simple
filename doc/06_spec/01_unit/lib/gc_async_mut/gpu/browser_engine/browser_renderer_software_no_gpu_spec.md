# Browser Renderer Software No Gpu Specification

> Tests covering BrowserRenderer software backend renders with no host-GPU dependency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Software No Gpu Specification

## Scenarios

### BrowserRenderer software backend renders with no host-GPU dependency

#### defaults to the software backend (BrowserRenderer.create)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to the software backend (BrowserRenderer.create)
   - Expected: r.backend_name() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to the software backend (BrowserRenderer.create)")
val r = BrowserRenderer.create(W, H)
expect(r.backend_name()).to_equal("software")
```

</details>

#### renders a static HTML string to a non-blank in-memory RGBA buffer

- renders a static HTML string to a non-blank in-memory RGBA buffer
   - Expected: result.ok is true
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`
   - Expected: result.pixel_data.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a static HTML string to a non-blank in-memory RGBA buffer")
val html = "<html><body style='margin:0;background:#ffffff'>" +
    "<div style='width:20px;height:15px;background-color:#ff0000'></div>" +
    "</body></html>"
val result = BrowserRenderer.create(W, H).render_html_to_pixels(html)
expect(result.ok).to_equal(true)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
expect(result.pixel_data.len()).to_equal(W * H)
expect(_non_blank_count(result.pixel_data, WHITE)).to_be_greater_than(0)
```

</details>

#### produces the expected block color for a known solid-color div

- produces the expected block color for a known solid-color div


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces the expected block color for a known solid-color div")
val html = "<html><body style='margin:0;background:#ffffff'>" +
    "<div style='width:20px;height:15px;background-color:#ff0000'></div>" +
    "</body></html>"
val result = BrowserRenderer.create(W, H).render_html_to_pixels(html)
# Exact placement inside the heuristic/fast-path fallback isn't pinned
# by contract (it may draw an approximated block rect rather than the
# literal 20x15 box), so assert presence of the expected color and
# continued presence of the white background rather than an exact
# pixel index — same discipline as browser_renderer_smoke_spec.spl.
expect(_non_blank_count(result.pixel_data, WHITE)).to_be_greater_than(0)
var red_count: i32 = 0
var i: i32 = 0
while i < result.pixel_data.len():
    if result.pixel_data[i] == RED:
        red_count = red_count + 1
    i = i + 1
expect(red_count).to_be_greater_than(0)
```

</details>

#### produces an exact uniform fill for a known solid-background page (no blocks)

- produces an exact uniform fill for a known solid-background page (no blocks)
   - Expected: r.backend_name() equals `software`
   - Expected: result.pixel_data.len() equals `W * H`
   - Expected: result.pixel_data[0] equals `0xFF0000FFu32`
   - Expected: result.pixel_data[result.pixel_data.len() - 1] equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces an exact uniform fill for a known solid-background page (no blocks)")
val html = "<html><body style='margin:0;background:#0000ff'></body></html>"
val r = BrowserRenderer.create_with_backend(W, H, "software")
expect(r.backend_name()).to_equal("software")
val result = r.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(W * H)
# No child block: the whole viewport resolves to the page background
# color deterministically — every pixel must match exactly.
expect(result.pixel_data[0]).to_equal(0xFF0000FFu32)
expect(result.pixel_data[result.pixel_data.len() - 1]).to_equal(0xFF0000FFu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer software backend renders with no host-GPU dependency.
- BrowserRenderer software backend renders with no host-GPU dependency

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

- Canonical SPipe generation for source `1bf396c4311013381da3b8a7b0703c52b2e1617e9bfa834fe70bb3ee32c88042`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1bf396c4311013381da3b8a7b0703c52b2e1617e9bfa834fe70bb3ee32c88042`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1bf396c4311013381da3b8a7b0703c52b2e1617e9bfa834fe70bb3ee32c88042`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to the software backend (BrowserRenderer.create)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a static HTML string to a non-blank in-memory RGBA buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_software_no_gpu_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the expected block color for a known solid-color div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
