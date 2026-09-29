# Backend Probe3d Strict Specification

> Tests covering Engine3D strict partial backend diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Probe3d Strict Specification

## Scenarios

### Engine3D strict partial backend diagnostics

#### reports CPU and software 3D paths as managed usable renderers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports CPU and software 3D paths as managed usable renderers
   - Expected: cpu.status equals `Engine3DBackendStatus.Initialized`
   - Expected: cpu.managed_session is true
   - Expected: cpu.has_compute is true
   - Expected: cpu.has_graphics is true
   - Expected: cpu.has_present is true
   - Expected: cpu.strict_failure_without_fallback() is true
   - Expected: software.status equals `Engine3DBackendStatus.Initialized`
   - Expected: software.api_name equals `software`
   - Expected: software.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CPU and software 3D paths as managed usable renderers")
val cpu = engine3d_strict_probe_backend("cpu")
val software = engine3d_strict_probe_backend("software")

expect(cpu.status).to_equal(Engine3DBackendStatus.Initialized)
expect(cpu.managed_session).to_equal(true)
expect(cpu.has_compute).to_equal(true)
expect(cpu.has_graphics).to_equal(true)
expect(cpu.has_present).to_equal(true)
expect(cpu.strict_failure_without_fallback()).to_equal(true)
expect(software.status).to_equal(Engine3DBackendStatus.Initialized)
expect(software.api_name).to_equal("software")
expect(software.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports CUDA ROCm HIP Metal Vulkan and WebGPU as managed but unavailable without fallback

- reports CUDA ROCm HIP Metal Vulkan and WebGPU as managed but unavailable without fallback
   - Expected: cuda.status equals `Engine3DBackendStatus.Unavailable`
   - Expected: cuda.shader_format equals `ptx`
   - Expected: cuda.managed_session is true
   - Expected: cuda.strict_failure_without_fallback() is true
   - Expected: rocm.shader_format equals `hsaco`
   - Expected: rocm.feature_gate equals `rocm_hip_3d_runtime`
   - Expected: hip.api_name equals `hip`
   - Expected: hip.strict_failure_without_fallback() is true
   - Expected: metal.shader_format equals `msl`
   - Expected: metal.has_present is true
   - Expected: vulkan.shader_format equals `spirv`
   - Expected: vulkan.has_graphics is true
   - Expected: webgpu.shader_format equals `wgsl`
   - Expected: webgpu.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CUDA ROCm HIP Metal Vulkan and WebGPU as managed but unavailable without fallback")
val prober = Engine3DBackendProber.create()
val cuda = prober.probe_backend("cuda")
val rocm = prober.probe_backend("rocm")
val hip = prober.probe_backend("hip")
val metal = prober.probe_backend("metal")
val vulkan = prober.probe_backend("vulkan")
val webgpu = prober.probe_backend("webgpu")

expect(cuda.status).to_equal(Engine3DBackendStatus.Unavailable)
expect(cuda.shader_format).to_equal("ptx")
expect(cuda.managed_session).to_equal(true)
expect(cuda.strict_failure_without_fallback()).to_equal(true)
expect(rocm.shader_format).to_equal("hsaco")
expect(rocm.feature_gate).to_equal("rocm_hip_3d_runtime")
expect(hip.api_name).to_equal("hip")
expect(hip.strict_failure_without_fallback()).to_equal(true)
expect(metal.shader_format).to_equal("msl")
expect(metal.has_present).to_equal(true)
expect(vulkan.shader_format).to_equal("spirv")
expect(vulkan.has_graphics).to_equal(true)
expect(webgpu.shader_format).to_equal("wgsl")
expect(webgpu.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports OpenCL as compute-only rather than a complete 3D raster backend

- reports OpenCL as compute-only rather than a complete 3D raster backend
   - Expected: probe.status equals `Engine3DBackendStatus.Unsupported`
   - Expected: probe.api_name equals `opencl`
   - Expected: probe.feature_gate equals `opencl_compute_only`
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports OpenCL as compute-only rather than a complete 3D raster backend")
val probe = engine3d_strict_probe_backend("opencl")

expect(probe.status).to_equal(Engine3DBackendStatus.Unsupported)
expect(probe.api_name).to_equal("opencl")
expect(probe.feature_gate).to_equal("opencl_compute_only")
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports OptiX as ray-tracing-only with no raster or present fallback

- reports OptiX as ray-tracing-only with no raster or present fallback
   - Expected: probe.status equals `Engine3DBackendStatus.Unsupported`
   - Expected: probe.api_name equals `optix`
   - Expected: probe.feature_gate equals `optix_ray_tracing_only`
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false
   - Expected: probe.has_ray_tracing is true
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports OptiX as ray-tracing-only with no raster or present fallback")
val probe = engine3d_strict_probe_backend("optix")

expect(probe.status).to_equal(Engine3DBackendStatus.Unsupported)
expect(probe.api_name).to_equal("optix")
expect(probe.feature_gate).to_equal("optix_ray_tracing_only")
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.has_ray_tracing).to_equal(true)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### summary includes all hardened partial 3D backend names

- summary includes all hardened partial 3D backend names


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("summary includes all hardened partial 3D backend names")
val summary = Engine3DBackendProber.create().probe_all_summary()

expect(summary).to_contain("requested=cpu")
expect(summary).to_contain("requested=software")
expect(summary).to_contain("requested=cuda")
expect(summary).to_contain("requested=rocm")
expect(summary).to_contain("requested=hip")
expect(summary).to_contain("requested=opencl")
expect(summary).to_contain("requested=metal")
expect(summary).to_contain("requested=vulkan")
expect(summary).to_contain("requested=webgpu")
expect(summary).to_contain("requested=optix")
```

</details>

#### proves CPU and software partial 3D frames with readback checksums

- proves CPU and software partial 3D frames with readback checksums
   - Expected: cpu.frame_rendered is true
   - Expected: cpu.status_code equals `frame-rendered`
   - Expected: cpu.readback_available is true
   - Expected: cpu.expected_checksum equals `cpu.actual_checksum`
   - Expected: software.frame_rendered is true
   - Expected: software.expected_checksum equals `software.actual_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("proves CPU and software partial 3D frames with readback checksums")
val cpu = engine3d_reference_render_evidence("cpu", 64, 32, 1)
val software = engine3d_reference_render_evidence("software", 64, 32, 2)

expect(cpu.frame_rendered).to_equal(true)
expect(cpu.status_code).to_equal("frame-rendered")
expect(cpu.readback_available).to_equal(true)
expect(cpu.expected_checksum).to_equal(cpu.actual_checksum)
expect(cpu.expected_checksum).to_be_greater_than(0)
expect(cpu.summary()).to_contain("rendered=true")
expect(software.frame_rendered).to_equal(true)
expect(software.expected_checksum).to_equal(software.actual_checksum)
```

</details>

#### keeps GPU partial 3D evidence unavailable until real readback exists

- keeps GPU partial 3D evidence unavailable until real readback exists
   - Expected: cuda.frame_rendered is false
   - Expected: cuda.status_code equals `backend-not-usable`
   - Expected: metal.frame_rendered is false
   - Expected: metal.status_code equals `backend-not-usable`
   - Expected: opencl.frame_rendered is false
   - Expected: opencl.status_code equals `backend-not-usable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps GPU partial 3D evidence unavailable until real readback exists")
val cuda = engine3d_reference_render_evidence("cuda", 64, 32, 1)
val metal = engine3d_reference_render_evidence("metal", 64, 32, 1)
val opencl = engine3d_reference_render_evidence("opencl", 64, 32, 1)

expect(cuda.frame_rendered).to_equal(false)
expect(cuda.status_code).to_equal("backend-not-usable")
expect(cuda.summary()).to_contain("rendered=false")
expect(metal.frame_rendered).to_equal(false)
expect(metal.status_code).to_equal("backend-not-usable")
expect(opencl.frame_rendered).to_equal(false)
expect(opencl.status_code).to_equal("backend-not-usable")
```

</details>

#### fails partial 3D render evidence closed on invalid readback

- fails partial 3D render evidence closed on invalid readback
   - Expected: no_readback.frame_rendered is false
   - Expected: no_readback.status_code equals `readback-unavailable`
   - Expected: mismatch.frame_rendered is false
   - Expected: mismatch.status_code equals `readback-mismatch`
   - Expected: no_draws.frame_rendered is false
   - Expected: no_draws.status_code equals `no-draw-calls`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails partial 3D render evidence closed on invalid readback")
val no_readback = engine3d_render_evidence_from_readback("cpu", 16, 16, 1, false, 123, 123)
val mismatch = engine3d_render_evidence_from_readback("cpu", 16, 16, 1, true, 123, 122)
val no_draws = engine3d_render_evidence_from_readback("cpu", 16, 16, 0, true, 123, 123)

expect(no_readback.frame_rendered).to_equal(false)
expect(no_readback.status_code).to_equal("readback-unavailable")
expect(mismatch.frame_rendered).to_equal(false)
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(no_draws.frame_rendered).to_equal(false)
expect(no_draws.status_code).to_equal("no-draw-calls")
```

</details>

#### requires runtime target buffer and sync evidence before frame readback is accepted

- requires runtime target buffer and sync evidence before frame readback is accepted
   - Expected: no_runtime.readback_available is false
   - Expected: no_runtime.status_code equals `runtime-device-unavailable`
   - Expected: no_target.status_code equals `missing-render-target-handle`
   - Expected: no_buffer.status_code equals `missing-readback-buffer-handle`
   - Expected: no_sync.status_code equals `readback-sync-incomplete`
   - Expected: ready.readback_available is true
   - Expected: ready.status_code equals `readback-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires runtime target buffer and sync evidence before frame readback is accepted")
val no_runtime = engine3d_readback_evidence("cpu", 16, 16, 1, false, 1, 2, true, 123, 123)
val no_target = engine3d_readback_evidence("cpu", 16, 16, 1, true, 0, 2, true, 123, 123)
val no_buffer = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 0, true, 123, 123)
val no_sync = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, false, 123, 123)
val ready = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 123)

expect(no_runtime.readback_available).to_equal(false)
expect(no_runtime.status_code).to_equal("runtime-device-unavailable")
expect(no_target.status_code).to_equal("missing-render-target-handle")
expect(no_buffer.status_code).to_equal("missing-readback-buffer-handle")
expect(no_sync.status_code).to_equal("readback-sync-incomplete")
expect(ready.readback_available).to_equal(true)
expect(ready.status_code).to_equal("readback-ready")
expect(ready.summary()).to_contain("target=1")
```

</details>

#### converts readback evidence into fail-closed render evidence

- converts readback evidence into fail-closed render evidence
   - Expected: rendered.frame_rendered is true
   - Expected: rendered.status_code equals `frame-rendered`
   - Expected: rejected.frame_rendered is false
   - Expected: rejected.status_code equals `readback-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts readback evidence into fail-closed render evidence")
val ready = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 123)
val rendered = engine3d_render_evidence_from_readback_evidence(ready)
val mismatch = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 122)
val rejected = engine3d_render_evidence_from_readback_evidence(mismatch)

expect(rendered.frame_rendered).to_equal(true)
expect(rendered.status_code).to_equal("frame-rendered")
expect(rejected.frame_rendered).to_equal(false)
expect(rejected.status_code).to_equal("readback-mismatch")
```

</details>

#### does not accept GPU readback handles while strict backend probe lacks real runtime evidence

- does not accept GPU readback handles while strict backend probe lacks real runtime evidence
   - Expected: cuda.status_code equals `backend-not-usable`
   - Expected: hip.status_code equals `backend-not-usable`
   - Expected: opencl.status_code equals `backend-not-usable`
   - Expected: metal.status_code equals `backend-not-usable`
   - Expected: vulkan.status_code equals `backend-not-usable`
   - Expected: webgpu.status_code equals `backend-not-usable`
   - Expected: optix.status_code equals `backend-not-usable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not accept GPU readback handles while strict backend probe lacks real runtime evidence")
val cuda = engine3d_readback_evidence("cuda", 16, 16, 1, true, 10, 11, true, 123, 123)
val hip = engine3d_readback_evidence("hip", 16, 16, 1, true, 10, 11, true, 123, 123)
val opencl = engine3d_readback_evidence("opencl", 16, 16, 1, true, 10, 11, true, 123, 123)
val metal = engine3d_readback_evidence("metal", 16, 16, 1, true, 10, 11, true, 123, 123)
val vulkan = engine3d_readback_evidence("vulkan", 16, 16, 1, true, 10, 11, true, 123, 123)
val webgpu = engine3d_readback_evidence("webgpu", 16, 16, 1, true, 10, 11, true, 123, 123)
val optix = engine3d_readback_evidence("optix", 16, 16, 1, true, 10, 11, true, 123, 123)

expect(cuda.status_code).to_equal("backend-not-usable")
expect(hip.status_code).to_equal("backend-not-usable")
expect(opencl.status_code).to_equal("backend-not-usable")
expect(metal.status_code).to_equal("backend-not-usable")
expect(vulkan.status_code).to_equal("backend-not-usable")
expect(webgpu.status_code).to_equal("backend-not-usable")
expect(optix.status_code).to_equal("backend-not-usable")
```

</details>

#### returns false when a 3D probe was substituted or demoted to Fallback

- returns false when a 3D probe was substituted or demoted to Fallback
   - Expected: substituted.requested_name equals `vulkan`
   - Expected: substituted.strict_failure_without_fallback() is false
   - Expected: demoted.selected_name equals `demoted.requested_name`
   - Expected: demoted.strict_failure_without_fallback() is false
   - Expected: engine3d_strict_probe_backend("vulkan").strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when a 3D probe was substituted or demoted to Fallback")
# Silent substitution: caller asked for vulkan, was handed cpu.
var substituted = engine3d_strict_probe_backend("vulkan")
substituted.selected_name = "cpu"
expect(substituted.requested_name).to_equal("vulkan")
expect(substituted.strict_failure_without_fallback()).to_equal(false)

# Status demotion: the backend name survived but the status did not.
var demoted = engine3d_strict_probe_backend("vulkan")
demoted.status = Engine3DBackendStatus.Fallback
expect(demoted.selected_name).to_equal(demoted.requested_name)
expect(demoted.strict_failure_without_fallback()).to_equal(false)

# Control: an untouched probe still passes, so the falses above come
# from the injected violation and not from something ambient here.
expect(engine3d_strict_probe_backend("vulkan").strict_failure_without_fallback()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine3D strict partial backend diagnostics.
- Engine3D strict partial backend diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `8b68b14077c199f06caf1cc39e4ca3257237bd716dd6e679e558418fe2461b8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b68b14077c199f06caf1cc39e4ca3257237bd716dd6e679e558418fe2461b8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b68b14077c199f06caf1cc39e4ca3257237bd716dd6e679e558418fe2461b8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports CPU and software 3D paths as managed usable renderers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports CUDA ROCm HIP Metal Vulkan and WebGPU as managed but unavailable without fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports OpenCL as compute-only rather than a complete 3D raster backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
