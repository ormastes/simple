# Helpers Availability Specification

> Tests covering Engine2D backend availability helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Availability Specification

## Scenarios

### Engine2D backend availability helpers

#### normalizes explicit platform native backend aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes explicit platform native backend aliases
   - Expected: backend_canonical_name("native") equals `baremetal`
   - Expected: backend_canonical_name("platform-native") equals `baremetal`
   - Expected: backend_canonical_name("virtio-gpu") equals `virtio_gpu`
   - Expected: backend_canonical_name("hip") equals `rocm`
   - Expected: backend_canonical_name("dx11") equals `directx`
   - Expected: backend_canonical_name("simd-cpu") equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes explicit platform native backend aliases")
expect(backend_canonical_name("native")).to_equal("baremetal")
expect(backend_canonical_name("platform-native")).to_equal("baremetal")
expect(backend_canonical_name("virtio-gpu")).to_equal("virtio_gpu")
expect(backend_canonical_name("hip")).to_equal("rocm")
expect(backend_canonical_name("dx11")).to_equal("directx")
expect(backend_canonical_name("simd-cpu")).to_equal("cpu_simd")
```

</details>

#### keeps explicit native backends ahead of auto probed backends

- keeps explicit native backends ahead of auto probed backends
   - Expected: explicit equals `["baremetal", "virtio_gpu"]`
   - Expected: full[0] equals `baremetal`
   - Expected: full[1] equals `virtio_gpu`
   - Expected: full[2] equals `metal`
   - Expected: auto_order[0] equals `metal`
   - Expected: auto_order equals `["metal", "cuda", "rocm", "qualcomm", "vulkan", "directx", "opencl", "opengl"... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps explicit native backends ahead of auto probed backends")
val explicit = backend_explicit_native_priority_order()
val full = backend_full_preference_order()
val auto_order = backend_default_priority_order()

expect(explicit).to_equal(["baremetal", "virtio_gpu"])
expect(full[0]).to_equal("baremetal")
expect(full[1]).to_equal("virtio_gpu")
expect(full[2]).to_equal("metal")
expect(auto_order[0]).to_equal("metal")
expect(auto_order).to_equal(["metal", "cuda", "rocm", "qualcomm", "vulkan", "directx", "opencl", "opengl", "intel", "webgpu", "cpu_simd", "software", "cpu"])
```

</details>

#### reports native backend priority and diagnostics without making them auto detected

- reports native backend priority and diagnostics without making them auto detected
   - Expected: backend_priority("baremetal") equals `-2`
   - Expected: backend_priority("virtio") equals `-1`
   - Expected: backend_display_name("baremetal") equals `Platform Native Framebuffer`
   - Expected: backend_display_name("virtio_gpu") equals `VirtIO GPU Framebuffer`
   - Expected: backend_display_name("directx") equals `DirectX (D3D11 via DXVK on Linux)`
   - Expected: backend_is_hardware("baremetal") is true
   - Expected: backend_is_hardware("directx") is true
   - Expected: backend_requires_gpu("baremetal") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports native backend priority and diagnostics without making them auto detected")
expect(backend_priority("baremetal")).to_equal(-2)
expect(backend_priority("virtio")).to_equal(-1)
expect(backend_display_name("baremetal")).to_equal("Platform Native Framebuffer")
expect(backend_display_name("virtio_gpu")).to_equal("VirtIO GPU Framebuffer")
expect(backend_display_name("directx")).to_equal("DirectX (D3D11 via DXVK on Linux)")
expect(backend_is_hardware("baremetal")).to_equal(true)
expect(backend_is_hardware("directx")).to_equal(true)
expect(backend_requires_gpu("baremetal")).to_equal(false)
expect(feature_gate_description("virtio_gpu")).to_contain("VirtIO GPU")
expect(feature_gate_description("directx")).to_contain("D3D11")
expect(backend_preference_summary()).to_contain("explicit native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D backend availability helpers.
- Engine2D backend availability helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `e96bf34fc3c2ef3d7cd5d5a7cb7e793b109fba6064b636c230344e1988a4e6d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e96bf34fc3c2ef3d7cd5d5a7cb7e793b109fba6064b636c230344e1988a4e6d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e96bf34fc3c2ef3d7cd5d5a7cb7e793b109fba6064b636c230344e1988a4e6d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/helpers_availability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/helpers_availability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/helpers_availability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes explicit platform native backend aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps explicit native backends ahead of auto probed backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports native backend priority and diagnostics without making them auto detected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
