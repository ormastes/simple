# Backend Webgpu Specification

> Tests covering engine2d WebGpuBackend (V3 M7 compile surface).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Webgpu Specification

## Scenarios

### engine2d WebGpuBackend (V3 M7 compile surface)

#### construction and trait conformance
_Exercises the full drawing surface of the backend stub._

#### constructs a stub backend without a WebGPU adapter

- constructs a stub backend without a WebGPU adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs a stub backend without a WebGPU adapter")
"""A freshly created backend must be inert until init()."""
var backend = WebGpuBackend.create()
expect(backend.initialized == false).to_be_true()
expect(backend.gpu_ready == false).to_be_true()
```

</details>

#### implements the RenderBackend trait end-to-end on a stub

- implements the RenderBackend trait end-to-end on a stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements the RenderBackend trait end-to-end on a stub")
"""Every trait method must be callable without a GPU."""
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
# HONESTY (site 11): init()'s return value now equals gpu_ready,
# not a bare true. This hermetic host has no real WebGPU adapter.
expect(ok == backend.gpu_ready).to_be_true()
expect(backend.name() == "webgpu").to_be_true()
expect(backend.width() == 32).to_be_true()
expect(backend.height() == 16).to_be_true()

# Drawing path must work even when no GPU is present - the
# CPU pixel buffer is the parity floor for M7.
backend.clear(0xFF202020u32)
backend.draw_rect_filled(0, 0, 8, 8, 0xFFFF0000u32)
backend.draw_rect(2, 2, 6, 6, 0xFF00FF00u32)
backend.draw_line(0, 0, 31, 15, 0xFF0000FFu32, 1)
backend.draw_circle(16, 8, 4, 0xFFFFFFFFu32)
backend.draw_circle_filled(24, 8, 3, 0xFFFF00FFu32)
backend.draw_rounded_rect(10, 2, 12, 10, 2, 0xFFFFFF00u32)
backend.draw_triangle_filled(0, 0, 8, 0, 4, 6, 0xFF00FFFFu32)
backend.draw_gradient_rect(0, 10, 32, 4, 0xFF000000u32, 0xFFFFFFFFu32)
backend.draw_text(1, 1, "M7", 0xFFFFFFFFu32, 7)
backend.draw_image(0, 0, 2, 2, [0u32, 0u32, 0u32, 0u32])
backend.set_clip(0, 0, 16, 8)
backend.clear_clip()
backend.present()

# read_pixels must return the drawn frame so compositor
# consumers keep working on hosts without a GPU adapter.
val pixels = backend.read_pixels()
expect(pixels.len() == 32 * 16).to_be_true()

backend.shutdown()
```

</details>

#### exposes draw_text_bg via Engine2DExtended

- exposes draw_text_bg via Engine2DExtended


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes draw_text_bg via Engine2DExtended")
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok == backend.gpu_ready).to_be_true()
backend.clear(0xFF000000u32)
backend.draw_text_bg(0, 0, "A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
backend.present()
backend.shutdown()
expect(true).to_be_true()
```

</details>

#### availability probe

#### reports webgpu_available() without crashing

- reports webgpu_available() without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports webgpu_available() without crashing")
# The SFFI stubs must answer the probe safely on hosts with
# no WebGPU runtime. We only check that the call returns
# (either true or false) - hermetic CI lacks an adapter.
val _available = webgpu_available()
expect(true).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering engine2d WebGpuBackend (V3 M7 compile surface).
- engine2d WebGpuBackend (V3 M7 compile surface)

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

- Canonical SPipe generation for source `1226535dd929efb04dc6ade65e77c73ea10a758db346cc3565a14edfb86c31df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1226535dd929efb04dc6ade65e77c73ea10a758db346cc3565a14edfb86c31df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1226535dd929efb04dc6ade65e77c73ea10a758db346cc3565a14edfb86c31df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a stub backend without a WebGPU adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements the RenderBackend trait end-to-end on a stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes draw_text_bg via Engine2DExtended' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
