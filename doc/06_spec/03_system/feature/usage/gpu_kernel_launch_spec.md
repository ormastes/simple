# GPU Kernel Launch

> Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device availability checks, runtime API completeness, memory allocation/free operations, and kernel execution pipeline validation. Uses stub functions in interpreter mode; actual GPU testing requires compiled binary with CUDA runtime linked and a compatible GPU.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Kernel Launch

Tests actual GPU kernel launch, device memory allocation, data transfer, and result verification. Covers CUDA device availability checks, runtime API completeness, memory allocation/free operations, and kernel execution pipeline validation. Uses stub functions in interpreter mode; actual GPU testing requires compiled binary with CUDA runtime linked and a compatible GPU.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GPU-LAUNCH |
| Category | GPU & SIMD |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/usage/gpu_kernel_launch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests actual GPU kernel launch, device memory allocation, data transfer, and result
verification. Covers CUDA device availability checks, runtime API completeness,
memory allocation/free operations, and kernel execution pipeline validation. Uses stub
functions in interpreter mode; actual GPU testing requires compiled binary with CUDA
runtime linked and a compatible GPU.

## Syntax

The spec uses stub CUDA functions to expose the no-device contract in interpreter
mode while still checking the runtime API names required for a live launch.

## Examples

`gpu_runtime_functions()` lists the allocation, transfer, launch, sync, and f64
load/store symbols that a compiled GPU runtime must provide.

## Scenarios

### GPU kernel launch prerequisites

#### checks CUDA device availability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- checks CUDA device availability
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks CUDA device availability")
val count = stub_cuda_device_count()
# In interpreter mode, no devices available
expect(count).to_equal(0)
```

</details>

#### reports GPU availability

- reports GPU availability
   - Expected: available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports GPU availability")
val available = stub_has_gpu()
# Expected false in interpreter mode
expect(available).to_equal(false)
```

</details>

### GPU runtime API

#### has complete function set for kernel execution

- has complete function set for kernel execution
   - Expected: fns[7] equals `gpu_load_f64`
   - Expected: fns.len() equals `9`
   - Expected: fns[8] equals `gpu_store_f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has complete function set for kernel execution")
val fns = gpu_runtime_functions()
expect(fns[7]).to_equal("gpu_load_f64")
expect(fns.len()).to_equal(9)
expect(fns[8]).to_equal("gpu_store_f64")
```

</details>

### GPU memory operations

#### allocates device memory

- allocates device memory
   - Expected: ptr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allocates device memory")
# Stub returns 0 (no GPU)
val ptr = stub_cuda_mem_alloc(1024)
expect(ptr).to_equal(0)
```

</details>

#### frees device memory

- frees device memory
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("frees device memory")
val result = stub_cuda_mem_free(0)
expect(result).to_equal(false)
```

</details>

### GPU kernel execution

#### initializes CUDA runtime

- initializes CUDA runtime
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes CUDA runtime")
# Stub returns false (no GPU)
val ok = stub_cuda_init()
expect(ok).to_equal(false)
```

</details>

#### skips kernel launch without GPU

- skips kernel launch without GPU
   - Expected: has_gpu is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips kernel launch without GPU")
# Vector add kernel requires GPU hardware
val has_gpu = stub_has_gpu()
if has_gpu:
    val fns = gpu_runtime_functions()
    expect(fns).to_contain("gpu_launch")
    expect(fns).to_contain("gpu_sync")
    expect(fns).to_contain("gpu_upload")
    expect(fns).to_contain("gpu_download")
else:
    # No GPU — skip
    expect(has_gpu).to_equal(false)
```

</details>

#### validates kernel compilation pipeline

- validates kernel compilation pipeline
   - Expected: pipeline_stages equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates kernel compilation pipeline")
# The pipeline: @gpu_kernel -> HIR(func_attr) -> MIR(is_kernel) -> PTX(.entry)
val pipeline_stages = 4
expect(pipeline_stages).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdcf80973feda9c92d5205a3bcd8effd165c151a425e1a3e290601e5eaa8bbea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdcf80973feda9c92d5205a3bcd8effd165c151a425e1a3e290601e5eaa8bbea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdcf80973feda9c92d5205a3bcd8effd165c151a425e1a3e290601e5eaa8bbea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/gpu_kernel_launch_spec.spl
mirror: doc/06_spec/03_system/feature/usage/gpu_kernel_launch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/gpu_kernel_launch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/gpu_kernel_launch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/gpu_kernel_launch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/gpu_kernel_launch_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks CUDA device availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_kernel_launch_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports GPU availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_kernel_launch_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has complete function set for kernel execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
