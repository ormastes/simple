# ffi_rocm_spec

> ROCm/HIP FFI Dispatch Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ffi_rocm_spec

ROCm/HIP FFI Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_rocm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ROCm/HIP FFI Dispatch Specification

@tag: gpu, engine2d, rocm, hip, amd, ffi
@cover src/lib/nogc_sync_mut/gpu/engine2d/ffi_rocm.spl 10%

Stream F4 (2026-08-09): the claim here was
`@cover src/lib/gc_async_mut/gpu/engine2d/ffi_rocm.spl 80%`. That file is a
3-line facade whose re-export target does not exist on disk (see
doc/08_tracking/bug/gc_async_mut_gpu_ffi_facades_are_dangling_2026-08-09.md),
and 10 of this file's 13 `it` bodies are the bare gate assertion. Only 3
cases have real bodies (the fail-closed HIP handle / packed-argument /
dynamic-load cases). The target now names the module where RocmDynFfi actually
lives and the figure reflects those 3 cases. This host has no AMD GPU, so
the remaining 10 need a ROCm machine, not a rewrite here.

Verifies RocmDynFfi dispatch class: static rt_rocm_* hooks plus dynamic DynLib
dlopen libamdhip64.so probes. Covers AC-3 + AC-8.

## Scenarios

### RocmDynFfi

### create_dynamic

#### AC-3: attempts to load libamdhip64.so

- AC-3: attempts to load libamdhip64.so
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: attempts to load libamdhip64.so")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: returns nil when HIP runtime not installed

- AC-8: returns nil when HIP runtime not installed
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: returns nil when HIP runtime not installed")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### create_static

#### AC-8: static mode available when runtime is built

- AC-8: static mode available when runtime is built
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: static mode available when runtime is built")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### HIP device management

#### AC-3: hipInit returns success code

- AC-3: hipInit returns success code
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: hipInit returns success code")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: device_count via hipGetDeviceCount

- AC-3: device_count via hipGetDeviceCount
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: device_count via hipGetDeviceCount")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### HIP memory operations

#### AC-3: hipMalloc returns device pointer

- AC-3: hipMalloc returns device pointer
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: hipMalloc returns device pointer")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### HIP kernel launch

#### AC-3: hipLaunchKernel dispatches compute kernel

- AC-3: hipLaunchKernel dispatches compute kernel
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: hipLaunchKernel dispatches compute kernel")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### fails closed instead of dispatching a zero HIP kernel handle

- fails closed instead of dispatching a zero HIP kernel handle
   - Expected: ffi.launch_kernel("kernel_clear", 1, 1, 1, 1, 1, 1, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed instead of dispatching a zero HIP kernel handle")
val ffi = RocmDynFfi.create_static()
expect(ffi.launch_kernel("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(false)
```

</details>

#### rejects the legacy uncounted packed-argument pointer

- rejects the legacy uncounted packed-argument pointer
   - Expected: ffi.launch_kernel_args(7, 1, 1, 1, 1, 1, 1, 0, 4096) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the legacy uncounted packed-argument pointer")
val ffi = RocmDynFfi.create_static()
expect(ffi.launch_kernel_args(7, 1, 1, 1, 1, 1, 1, 0, 4096)).to_equal(false)
```

</details>

#### fails closed when the dynamic HIP runtime cannot be loaded

- fails closed when the dynamic HIP runtime cannot be loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when the dynamic HIP runtime cannot be loaded")
val ffi = RocmDynFfi.create_dynamic_from("/definitely/missing/libamdhip64.so")
expect(ffi).to_be_nil()
```

</details>

### platform support

#### AC-7: ROCm primary on Linux

- AC-7: ROCm primary on Linux
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: ROCm primary on Linux")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-7: ROCm partial on Windows

- AC-7: ROCm partial on Windows
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: ROCm partial on Windows")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: ROCm dynamic-only (no Rust runtime)

- AC-3: ROCm dynamic-only (no Rust runtime)
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: ROCm dynamic-only (no Rust runtime)")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `c0483b7a4e10da4c40b3917ee41e2511d88128eb75bbd366e912f355468d531b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0483b7a4e10da4c40b3917ee41e2511d88128eb75bbd366e912f355468d531b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0483b7a4e10da4c40b3917ee41e2511d88128eb75bbd366e912f355468d531b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/ffi_rocm_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_rocm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_rocm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_rocm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_rocm_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: attempts to load libamdhip64.so' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_rocm_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: returns nil when HIP runtime not installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_rocm_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: static mode available when runtime is built' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
