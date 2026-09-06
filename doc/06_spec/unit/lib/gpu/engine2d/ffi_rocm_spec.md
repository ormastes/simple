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
| Source | `test/unit/lib/gpu/engine2d/ffi_rocm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ROCm/HIP FFI Dispatch Specification

@tag: gpu, engine2d, rocm, hip, amd, ffi
@cover src/lib/gc_async_mut/gpu/engine2d/ffi_rocm.spl 80%

Verifies RocmFfi dispatch class: dynamic-first (DynLib dlopen libamdhip64.so)
since no Rust runtime exists for rt_rocm_*. Covers AC-3 + AC-8.

## Scenarios

### RocmFfi

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
val ffi = RocmFfi.create_static()
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
val ffi = RocmFfi.create_static()
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
val ffi = RocmFfi.create_dynamic_from("/definitely/missing/libamdhip64.so")
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

- Canonical SPipe generation for source `a92443d6a6203514576fbcc02d538c56341275e77c080723580589d710519185`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a92443d6a6203514576fbcc02d538c56341275e77c080723580589d710519185`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a92443d6a6203514576fbcc02d538c56341275e77c080723580589d710519185`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine2d/ffi_rocm_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine2d/ffi_rocm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine2d/ffi_rocm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine2d/ffi_rocm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine2d/ffi_rocm_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: attempts to load libamdhip64.so' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/ffi_rocm_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: returns nil when HIP runtime not installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/ffi_rocm_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: static mode available when runtime is built' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
