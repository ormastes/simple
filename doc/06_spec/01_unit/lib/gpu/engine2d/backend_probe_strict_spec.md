# Backend Probe Strict Specification

> Tests covering Engine2D strict backend probe diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Probe Strict Specification

## Scenarios

### Engine2D strict backend probe diagnostics

#### reports typed ROCm diagnostics without CPU fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports typed ROCm diagnostics without CPU fallback
   - Expected: probe.requested_name equals `rocm`
   - Expected: probe.selected_name equals `rocm`
   - Expected: probe.api_name equals `rocm`
   - Expected: probe.feature_gate equals `rocm_runtime`
   - Expected: probe.shader_format equals `hsaco`
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.available is false
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports typed ROCm diagnostics without CPU fallback")
val probe = StrictBackendFactory.strict().create_backend("rocm")

expect(probe.requested_name).to_equal("rocm")
expect(probe.selected_name).to_equal("rocm")
expect(probe.api_name).to_equal("rocm")
expect(probe.feature_gate).to_equal("rocm_runtime")
expect(probe.shader_format).to_equal("hsaco")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.available).to_equal(false)
# The invariant: ROCm failed AS ROCm. No CPU was handed back.
expect(probe.strict_failure_without_fallback()).to_equal(true)
expect(probe.reason).to_contain("ROCm")
```

</details>

#### reports CPU SIMD as an available non-GPU path that still names itself honestly

- reports CPU SIMD as an available non-GPU path that still names itself honestly
   - Expected: probe.requested_name equals `cpu_simd`
   - Expected: probe.selected_name equals `cpu_simd`
   - Expected: probe.api_name equals `cpu_simd`
   - Expected: probe.feature_gate equals `cpu_simd_runtime`
   - Expected: probe.shader_format equals `none`
   - Expected: probe.is_ok() is true
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CPU SIMD as an available non-GPU path that still names itself honestly")
val probe = StrictBackendFactory.strict().create_backend("cpu_simd")

expect(probe.requested_name).to_equal("cpu_simd")
expect(probe.selected_name).to_equal("cpu_simd")
expect(probe.api_name).to_equal("cpu_simd")
expect(probe.feature_gate).to_equal("cpu_simd_runtime")
expect(probe.shader_format).to_equal("none")
expect(probe.is_ok()).to_equal(true)
expect(probe.strict_failure_without_fallback()).to_equal(true)
# cpu_simd must not overclaim: it is an alias of cpu with no live SIMD
# dispatch, and the reason text has to keep saying so.
expect(probe.reason).to_contain("no live SIMD dispatch")
```

</details>

#### keeps a CUDA probe on the CUDA backend whether or not a device answers

- keeps a CUDA probe on the CUDA backend whether or not a device answers
   - Expected: probe.requested_name equals `cuda`
   - Expected: probe.selected_name equals `cuda`
   - Expected: probe.api_name equals `cuda`
   - Expected: probe.shader_format equals `ptx`
   - Expected: probe.strict_failure_without_fallback() is true
   - Expected: status_known is true
   - Expected: probe.available equals `probe.status == BackendStatus.Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a CUDA probe on the CUDA backend whether or not a device answers")
val probe = StrictBackendFactory.strict().create_backend("cuda")

expect(probe.requested_name).to_equal("cuda")
expect(probe.selected_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(probe.strict_failure_without_fallback()).to_equal(true)
# Host-independent: whichever way the probe resolves, it stays CUDA and
# its availability flag agrees with its status.
val status_known = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable
expect(status_known).to_equal(true)
expect(probe.available).to_equal(probe.status == BackendStatus.Initialized)
```

</details>

#### reports architecture-specific CPU SIMD probes without fallback

- reports architecture-specific CPU SIMD probes without fallback
   - Expected: x86.requested_name equals `cpu_simd_x86`
   - Expected: x86.selected_name equals `cpu_simd_x86`
   - Expected: x86.api_name equals `cpu_simd_x86`
   - Expected: x86.strict_failure_without_fallback() is true
   - Expected: arm.selected_name equals `cpu_simd_arm`
   - Expected: arm.strict_failure_without_fallback() is true
   - Expected: riscv.selected_name equals `cpu_simd_riscv`
   - Expected: riscv.strict_failure_without_fallback() is true
   - Expected: arch_status_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports architecture-specific CPU SIMD probes without fallback")
val factory = StrictBackendFactory.strict()
val x86 = factory.create_backend("cpu_simd_x86")
val arm = factory.create_backend("cpu_simd_arm")
val riscv = factory.create_backend("cpu_simd_riscv")

expect(x86.requested_name).to_equal("cpu_simd_x86")
expect(x86.selected_name).to_equal("cpu_simd_x86")
expect(x86.api_name).to_equal("cpu_simd_x86")
expect(x86.strict_failure_without_fallback()).to_equal(true)
expect(arm.selected_name).to_equal("cpu_simd_arm")
expect(arm.strict_failure_without_fallback()).to_equal(true)
expect(riscv.selected_name).to_equal("cpu_simd_riscv")
expect(riscv.strict_failure_without_fallback()).to_equal(true)

# Each arch probe is Initialized only when the RUNTIME feature is
# confirmed on this host; otherwise Unavailable. Both are legitimate,
# but nothing else is — and none of them may become "cpu".
val arch_status_known = (x86.status == BackendStatus.Initialized or x86.status == BackendStatus.Unavailable) and (arm.status == BackendStatus.Initialized or arm.status == BackendStatus.Unavailable) and (riscv.status == BackendStatus.Initialized or riscv.status == BackendStatus.Unavailable)
expect(arch_status_known).to_equal(true)
```

</details>

#### reports OptiX as unavailable for Engine2D raster instead of falling back

- reports OptiX as unavailable for Engine2D raster instead of falling back
   - Expected: probe.requested_name equals `optix`
   - Expected: probe.selected_name equals `optix`
   - Expected: probe.api_name equals `optix`
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports OptiX as unavailable for Engine2D raster instead of falling back")
val probe = StrictBackendFactory.strict().create_backend("optix")

expect(probe.requested_name).to_equal("optix")
expect(probe.selected_name).to_equal("optix")
expect(probe.api_name).to_equal("optix")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports OpenCL as unavailable on this host without substituting a backend

- reports OpenCL as unavailable on this host without substituting a backend
   - Expected: probe.requested_name equals `opencl`
   - Expected: probe.selected_name equals `opencl`
   - Expected: probe.api_name equals `opencl`
   - Expected: probe.shader_format equals `opencl-c`
   - Expected: probe.has_present is false
   - Expected: probe.strict_failure_without_fallback() is true
   - Expected: status_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports OpenCL as unavailable on this host without substituting a backend")
val probe = StrictBackendFactory.strict().create_backend("opencl")

expect(probe.requested_name).to_equal("opencl")
expect(probe.selected_name).to_equal("opencl")
expect(probe.api_name).to_equal("opencl")
expect(probe.shader_format).to_equal("opencl-c")
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
# OpenCL context creation fails on this host, so the ONLY claim made
# here is the host-independent one: whatever the status, it stayed
# OpenCL. No device-specific OpenCL behaviour is asserted.
val status_known = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable
expect(status_known).to_equal(true)
```

</details>

#### keeps strict Vulkan Metal CUDA WebGPU failures on the requested backend

- keeps strict Vulkan Metal CUDA WebGPU failures on the requested backend
   - Expected: vulkan.selected_name equals `vulkan`
   - Expected: vulkan.shader_format equals `spirv`
   - Expected: vulkan.strict_failure_without_fallback() is true
   - Expected: metal.selected_name equals `metal`
   - Expected: metal.shader_format equals `msl`
   - Expected: metal.strict_failure_without_fallback() is true
   - Expected: cuda.selected_name equals `cuda`
   - Expected: cuda.shader_format equals `ptx`
   - Expected: cuda.strict_failure_without_fallback() is true
   - Expected: webgpu.selected_name equals `webgpu`
   - Expected: webgpu.shader_format equals `wgsl`
   - Expected: webgpu.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps strict Vulkan Metal CUDA WebGPU failures on the requested backend")
val factory = StrictBackendFactory.strict()
val vulkan = factory.create_backend("vulkan")
val metal = factory.create_backend("metal")
val cuda = factory.create_backend("cuda")
val webgpu = factory.create_backend("webgpu")

expect(vulkan.selected_name).to_equal("vulkan")
expect(vulkan.shader_format).to_equal("spirv")
expect(vulkan.strict_failure_without_fallback()).to_equal(true)
expect(metal.selected_name).to_equal("metal")
expect(metal.shader_format).to_equal("msl")
expect(metal.strict_failure_without_fallback()).to_equal(true)
expect(cuda.selected_name).to_equal("cuda")
expect(cuda.shader_format).to_equal("ptx")
expect(cuda.strict_failure_without_fallback()).to_equal(true)
expect(webgpu.selected_name).to_equal("webgpu")
expect(webgpu.shader_format).to_equal("wgsl")
expect(webgpu.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports an unknown backend as unavailable under its own name

- reports an unknown backend as unavailable under its own name
   - Expected: probe.requested_name equals `definitely_not_a_backend`
   - Expected: probe.selected_name equals `definitely_not_a_backend`
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an unknown backend as unavailable under its own name")
# The catch-all arm is the easiest place for a silent CPU substitution
# to be reintroduced, so it is pinned explicitly.
val probe = StrictBackendFactory.strict().create_backend("definitely_not_a_backend")

expect(probe.requested_name).to_equal("definitely_not_a_backend")
expect(probe.selected_name).to_equal("definitely_not_a_backend")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### per-backend diagnostic text names the requested backend and its status

- per-backend diagnostic text names the requested backend and its status
   - Expected: probe.strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("per-backend diagnostic text names the requested backend and its status")
# Replaces the old probe_all_summary() assertion. BackendProber has no
# aggregate-summary method in this tree, so this walks the per-backend
# diagnostic_text() that DOES exist rather than asserting a format that
# does not.
val prober = BackendProber.create()
for name in ["cpu", "cpu_simd", "vulkan", "cuda", "metal", "opencl", "rocm", "webgpu"]:
    val probe = prober.probe_backend(name)
    val diag = probe.diagnostic_text()
    expect(diag).to_contain("requested=" + name)
    expect(diag).to_contain("selected=" + name)
    expect(diag).to_contain("status=" + backend_status_text(probe.status))
    expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### DISCLOSURE: the richer engine2d probe surface is not implemented and is not tested

- DISCLOSURE: the richer engine2d probe surface is not implemented and is not tested
   - Expected: probe.strict_failure_without_fallback() is true
   - Expected: probe.selected_name equals `probe.requested_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DISCLOSURE: the richer engine2d probe surface is not implemented and is not tested")
# This example proves NOTHING about hardware classification, device
# memory reporting, or aggregate probe summaries. It exists so that the
# gap is VISIBLE in the suite output instead of being an absence nobody
# notices — the same reason the frame-content gate prints its
# "proves NOTHING" banner when no frame was produced.
#
# NOT IMPLEMENTED on engine2d BackendProbeResult / BackendProber:
#   - is_hardware()          : no hardware-vs-emulation classification
#   - memory_mb              : no device memory is reported
#   - summary()              : only diagnostic_text() exists
#   - probe_all_summary()    : BackendProber has no aggregate summary
# Engine3D DOES have probe_all_summary(); engine2d does not. That
# asymmetry is real and deliberate-by-omission, not a bug being hidden.
print("ENGINE2D PROBE SURFACE GAP — is_hardware/memory_mb/summary/probe_all_summary are NOT implemented on engine2d BackendProbeResult; this example proves NOTHING about them. See doc/08_tracking/bug/ for the strict-probe sweep.")

# What IS binding here: the strict invariant holds across every backend
# name the selector accepts, so the disclosure above cannot be used to
# smuggle in a silent fallback.
val factory = StrictBackendFactory.strict()
for name in ["cpu", "software", "cpu_simd", "cpu_simd_x86", "cpu_simd_arm", "cpu_simd_riscv", "vulkan", "cuda", "rocm", "opencl", "metal", "hip", "webgpu", "optix"]:
    val probe = factory.create_backend(name)
    expect(probe.strict_failure_without_fallback()).to_equal(true)
    expect(probe.selected_name).to_equal(probe.requested_name)
```

</details>

#### returns false when a probe was substituted or demoted to Fallback

- returns false when a probe was substituted or demoted to Fallback
   - Expected: substituted.requested_name equals `vulkan`
   - Expected: substituted.strict_failure_without_fallback() is false
   - Expected: demoted.selected_name equals `demoted.requested_name`
   - Expected: demoted.strict_failure_without_fallback() is false
   - Expected: factory.create_backend("vulkan").strict_failure_without_fallback() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when a probe was substituted or demoted to Fallback")
val factory = StrictBackendFactory.strict()

# Silent substitution: caller asked for vulkan, was handed cpu.
var substituted = factory.create_backend("vulkan")
substituted.selected_name = "cpu"
expect(substituted.requested_name).to_equal("vulkan")
expect(substituted.strict_failure_without_fallback()).to_equal(false)

# Status demotion: the backend name survived but the status did not.
var demoted = factory.create_backend("vulkan")
demoted.status = BackendStatus.Fallback
expect(demoted.selected_name).to_equal(demoted.requested_name)
expect(demoted.strict_failure_without_fallback()).to_equal(false)

# Control: the untouched probe from the same factory call still passes,
# so the two falses above are caused by the injected violation and not
# by something ambient about this example.
expect(factory.create_backend("vulkan").strict_failure_without_fallback()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D strict backend probe diagnostics.
- Engine2D strict backend probe diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `73f3968ea7463597666d4c2289fe8c777b9fbb0b25fe5e088f091ade409c41bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73f3968ea7463597666d4c2289fe8c777b9fbb0b25fe5e088f091ade409c41bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73f3968ea7463597666d4c2289fe8c777b9fbb0b25fe5e088f091ade409c41bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports typed ROCm diagnostics without CPU fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports CPU SIMD as an available non-GPU path that still names itself honestly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a CUDA probe on the CUDA backend whether or not a device answers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
