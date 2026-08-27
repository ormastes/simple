# Backend Webgpu Specification

> Tests covering engine2d WebGpuBackend (V3 M7 compile surface).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Webgpu Specification

## Scenarios

### engine2d WebGpuBackend (V3 M7 compile surface)

#### construction and trait conformance
_Exercises the full drawing surface of the backend stub._

#### constructs a stub backend without a WebGPU adapter

- constructs a stub backend without a WebGPU adapter
   - Expected: backend.initialized is false
   - Expected: backend.gpu_ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a stub backend without a WebGPU adapter")
"""A freshly created backend must be inert until init()."""
var backend = WebGpuBackend.create()
expect(backend.initialized).to_equal(false)
expect(backend.gpu_ready).to_equal(false)
```

</details>

#### implements the RenderBackend trait end-to-end on a stub

- implements the RenderBackend trait end-to-end on a stub
   - Expected: ok equals `backend.gpu_ready`
   - Expected: ok is false
   - Expected: backend.name() equals `webgpu`
   - Expected: backend.width() equals `32`
   - Expected: backend.height() equals `16`
   - Expected: pixels.len() equals `32 * 16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("implements the RenderBackend trait end-to-end on a stub")
"""Every trait method must be callable without a GPU."""
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
# Honest availability result (site 11): equals gpu_ready, not a
# bare true. This hermetic host has no real WebGPU adapter.
expect(ok).to_equal(backend.gpu_ready)
expect(ok).to_equal(false)
expect(backend.name()).to_equal("webgpu")
expect(backend.width()).to_equal(32)
expect(backend.height()).to_equal(16)

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
expect(pixels.len()).to_equal(32 * 16)

backend.shutdown()
```

</details>

#### exposes draw_text_bg via Engine2DExtended

- exposes draw_text_bg via Engine2DExtended
   - Expected: ok equals `backend.gpu_ready`
   - Expected: pixels[0] equals `expected.pixels[0]`
   - Expected: pixels[1] equals `expected.pixels[1]`
   - Expected: pixels[32] equals `expected.pixels[expected.width]`
   - Expected: pixels[33] equals `expected.pixels[expected.width + 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes draw_text_bg via Engine2DExtended")
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok).to_equal(backend.gpu_ready)
backend.clear(0xFF000000u32)
backend.draw_text_bg(0, 0, "A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
val pixels = backend.read_pixels()
val expected = text_blit_buffer("A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
expect(pixels[0]).to_equal(expected.pixels[0])
expect(pixels[1]).to_equal(expected.pixels[1])
expect(pixels[32]).to_equal(expected.pixels[expected.width])
expect(pixels[33]).to_equal(expected.pixels[expected.width + 1])
backend.present()
backend.shutdown()
```

</details>

#### routes foreground draw_text through shared transparent text semantics

- routes foreground draw_text through shared transparent text semantics
   - Expected: ok equals `backend.gpu_ready`
   - Expected: fg_count > 0 is true
   - Expected: bg_count > 0 is true
   - Expected: transparent_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes foreground draw_text through shared transparent text semantics")
var backend = WebGpuBackend.create()
val ok = backend.init(8, 8)
expect(ok).to_equal(backend.gpu_ready)
val bg = 0xFF303030u32
backend.clear(bg)

backend.draw_text(0, 0, "I", 0xFFFFFFFFu32, 7)
val pixels = backend.read_pixels()
val expected = text_render_to_buf("I", 0xFFFFFFFFu32, 0u32, 7)
var fg_count = 0
var bg_count = 0
var transparent_count = 0
var idx = 0
while idx < pixels.len():
    if pixels[idx] == 0xFFFFFFFFu32:
        fg_count = fg_count + 1
    if pixels[idx] == bg:
        bg_count = bg_count + 1
    idx = idx + 1
idx = 0
while idx < expected.len():
    if expected[idx] == 0u32:
        transparent_count = transparent_count + 1
    idx = idx + 1

expect(fg_count > 0).to_equal(true)
expect(bg_count > 0).to_equal(true)
expect(transparent_count > 0).to_equal(true)
backend.shutdown()
```

</details>

#### availability probe

#### reports webgpu_available() without crashing

- reports webgpu_available() without crashing
   - Expected: backend.name() equals `webgpu`
   - Expected: backend.init(1, 1) equals `backend.gpu_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports webgpu_available() without crashing")
# The SFFI stubs must answer the probe safely on hosts with
# no WebGPU runtime. We only check that the call returns
# (either true or false) - hermetic CI lacks an adapter.
val _available = webgpu_available()
var backend = WebGpuBackend.create()
expect(backend.name()).to_equal("webgpu")
expect(backend.init(1, 1)).to_equal(backend.gpu_ready)
backend.shutdown()
```

</details>

#### un-initialized backend probes Unavailable, not ready

- un-initialized backend probes Unavailable, not ready
   - Expected: backend.gpu_ready is false
   - Expected: backend_status_text(probe.status) equals `Unavailable`
   - Expected: probe.reason.len() > 0 is true
   - Expected: backend_status_text(probe2.status) equals `Unavailable`
   - Expected: backend_status_text(probe2.status) equals `Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("un-initialized backend probes Unavailable, not ready")
"""Honesty (mirrors probe_directx): a freshly created backend has no
live GPU surface, so probe() must report Unavailable with a recorded
reason rather than claiming the GPU path is ready."""
var backend = WebGpuBackend.create()
expect(backend.gpu_ready).to_equal(false)
val probe = backend.probe()
expect(backend_status_text(probe.status)).to_equal("Unavailable")
expect(probe.reason.len() > 0).to_equal(true)
# After init on an adapterless host the surface is still not live, so
# probe stays honest. On a host that DID acquire a GPU surface it must
# instead report Initialized — never a false "ready" without a surface.
backend.init(4, 4)
val probe2 = backend.probe()
if not backend.gpu_ready:
    expect(backend_status_text(probe2.status)).to_equal("Unavailable")
else:
    expect(backend_status_text(probe2.status)).to_equal("Initialized")
backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering engine2d WebGpuBackend (V3 M7 compile surface).
- engine2d WebGpuBackend (V3 M7 compile surface)

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

- Canonical SPipe generation for source `3221eb8f68a17340fd42a7010f2d9ec3f228ead5f355e278bd274d9f0aeb436c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3221eb8f68a17340fd42a7010f2d9ec3f228ead5f355e278bd274d9f0aeb436c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3221eb8f68a17340fd42a7010f2d9ec3f228ead5f355e278bd274d9f0aeb436c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a stub backend without a WebGPU adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements the RenderBackend trait end-to-end on a stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes draw_text_bg via Engine2DExtended' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
