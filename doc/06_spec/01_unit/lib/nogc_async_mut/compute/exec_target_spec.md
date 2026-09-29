# Exec Target Specification

> Tests covering ExecTarget two-level resolver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exec Target Specification

## Scenarios

### ExecTarget two-level resolver

#### cpu class always resolves to scalar

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cpu class always resolves to scalar
- Resolve cpu on a machine with no accelerators
   - Expected: compute_backend_name(t.backend) equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cpu class always resolves to scalar")
step("Resolve cpu on a machine with no accelerators")
val t = resolve_exec_target(ComputeDeviceClass.Cpu, ComputeBackend.NoneBackend, EnforceMode.Suggest, BackendCaps.none())
expect(compute_backend_name(t.backend)).to_equal("scalar")
expect(t.resolved).to_be(true)
```

</details>

#### gpu auto-picks best backend in landed order (vulkan over cuda)

- gpu auto-picks best backend in landed order (vulkan over cuda)
- Resolve gpu when both vulkan and cuda are present
   - Expected: compute_backend_name(t.backend) equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gpu auto-picks best backend in landed order (vulkan over cuda)")
step("Resolve gpu when both vulkan and cuda are present")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Suggest, caps_vulkan_and_cuda())
expect(compute_backend_name(t.backend)).to_equal("vulkan")
expect(t.resolved).to_be(true)
```

</details>

#### gpu picks cuda when it is the only gpu

- gpu picks cuda when it is the only gpu
   - Expected: compute_backend_name(t.backend) equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gpu picks cuda when it is the only gpu")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Suggest, caps_cuda_only())
expect(compute_backend_name(t.backend)).to_equal("cuda")
```

</details>

#### require gpu with no gpu fails closed (resolved=false)

- require gpu with no gpu fails closed (resolved=false)
- require enforcement must NOT silently downgrade
   - Expected: compute_backend_name(t.backend) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("require gpu with no gpu fails closed (resolved=false)")
step("require enforcement must NOT silently downgrade")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Require, BackendCaps.none())
expect(t.resolved).to_be(false)
expect(compute_backend_name(t.backend)).to_equal("none")
```

</details>

#### suggest gpu with no gpu falls back to pure_simple (resolved=true)

- suggest gpu with no gpu falls back to pure_simple (resolved=true)
   - Expected: compute_backend_name(t.backend) equals `pure_simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("suggest gpu with no gpu falls back to pure_simple (resolved=true)")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.NoneBackend, EnforceMode.Suggest, BackendCaps.none())
expect(t.resolved).to_be(true)
expect(compute_backend_name(t.backend)).to_equal("pure_simple")
```

</details>

#### explicit backend require honored when available

- explicit backend require honored when available
- require cuda when cuda present
   - Expected: compute_backend_name(t.backend) equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("explicit backend require honored when available")
step("require cuda when cuda present")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.Cuda, EnforceMode.Require, caps_vulkan_and_cuda())
expect(compute_backend_name(t.backend)).to_equal("cuda")
expect(t.resolved).to_be(true)
```

</details>

#### explicit backend require fails closed when absent

- explicit backend require fails closed when absent
- require metal on a cuda-only machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("explicit backend require fails closed when absent")
step("require metal on a cuda-only machine")
val t = resolve_exec_target(ComputeDeviceClass.Gpu, ComputeBackend.Metal, EnforceMode.Require, caps_cuda_only())
expect(t.resolved).to_be(false)
```

</details>

#### simd umbrella lowers to gpu when present

- simd umbrella lowers to gpu when present
   - Expected: compute_backend_name(t.backend) equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd umbrella lowers to gpu when present")
val t = resolve_exec_target(ComputeDeviceClass.Simd, ComputeBackend.NoneBackend, EnforceMode.Suggest, caps_metal_only())
expect(compute_backend_name(t.backend)).to_equal("metal")
```

</details>

#### simd_cpu require fails closed without a simd cpu backend

- simd_cpu require fails closed without a simd cpu backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_cpu require fails closed without a simd cpu backend")
val t = resolve_exec_target(ComputeDeviceClass.SimdCpu, ComputeBackend.NoneBackend, EnforceMode.Require, BackendCaps.none())
expect(t.resolved).to_be(false)
```

</details>

#### default resolves to cpu on a bare machine

- default resolves to cpu on a bare machine
   - Expected: compute_backend_name(t.backend) equals `pure_simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default resolves to cpu on a bare machine")
val t = resolve_exec_target(ComputeDeviceClass.Default, ComputeBackend.NoneBackend, EnforceMode.Suggest, BackendCaps.none())
expect(compute_backend_name(t.backend)).to_equal("pure_simple")
```

</details>

#### parses device class names

- parses device class names
   - Expected: device_class_text(parse_device_class("simd_cpu")) equals `simd_cpu`
   - Expected: device_class_text(parse_device_class("gpu")) equals `gpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses device class names")
expect(device_class_text(parse_device_class("simd_cpu"))).to_equal("simd_cpu")
expect(device_class_text(parse_device_class("gpu"))).to_equal("gpu")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/compute/exec_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ExecTarget two-level resolver.
- ExecTarget two-level resolver

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `183451368ad32b23a219fcbf528f7188598ff97179b3a298783fce43e0d16bf3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `183451368ad32b23a219fcbf528f7188598ff97179b3a298783fce43e0d16bf3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `183451368ad32b23a219fcbf528f7188598ff97179b3a298783fce43e0d16bf3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/compute/exec_target_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/compute/exec_target_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/compute/exec_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/compute/exec_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/compute/exec_target_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu class always resolves to scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/compute/exec_target_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gpu auto-picks best backend in landed order (vulkan over cuda)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/compute/exec_target_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gpu picks cuda when it is the only gpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
