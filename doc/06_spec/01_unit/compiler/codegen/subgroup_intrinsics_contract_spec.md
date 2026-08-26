# Subgroup Intrinsics Contract Specification

> Tests covering subgroup intrinsics contract — OpenCL backend, subgroup intrinsics contract — CUDA/PTX backend, gpu_intrinsics — subgroup recognition and arity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Subgroup Intrinsics Contract Specification

## Scenarios

### subgroup intrinsics contract — OpenCL backend

#### emits get_sub_group_local_id() for gpu_lane_id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits get_sub_group_local_id() for gpu_lane_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits get_sub_group_local_id() for gpu_lane_id")
val func = make_opencl_subgroup_kernel("sg_lane_id_kernel", 100, lane_id_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("get_sub_group_local_id()")
```

</details>

#### emits get_sub_group_id() for gpu_warp_id

- emits get_sub_group_id() for gpu_warp_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits get_sub_group_id() for gpu_warp_id")
val func = make_opencl_subgroup_kernel("sg_warp_id_kernel", 101, warp_id_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("get_sub_group_id()")
```

</details>

#### emits get_sub_group_size() for gpu_warp_size

- emits get_sub_group_size() for gpu_warp_size


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits get_sub_group_size() for gpu_warp_size")
val func = make_opencl_subgroup_kernel("sg_warp_size_kernel", 102, warp_size_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("get_sub_group_size()")
```

</details>

#### emits sub_group_shuffle for gpu_warp_shuffle

- emits sub_group_shuffle for gpu_warp_shuffle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_shuffle for gpu_warp_shuffle")
val func = make_opencl_subgroup_kernel("sg_shuffle_kernel", 103, warp_shuffle_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_shuffle(")
```

</details>

#### emits sub_group_shuffle_down for gpu_warp_shuffle_down

- emits sub_group_shuffle_down for gpu_warp_shuffle_down


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_shuffle_down for gpu_warp_shuffle_down")
val func = make_opencl_subgroup_kernel("sg_shuffle_down_kernel", 104, warp_shuffle_down_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_shuffle_down(")
```

</details>

#### emits sub_group_shuffle_up for gpu_warp_shuffle_up

- emits sub_group_shuffle_up for gpu_warp_shuffle_up


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_shuffle_up for gpu_warp_shuffle_up")
val func = make_opencl_subgroup_kernel("sg_shuffle_up_kernel", 105, warp_shuffle_up_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_shuffle_up(")
```

</details>

#### emits sub_group_shuffle_xor for gpu_warp_shuffle_xor

- emits sub_group_shuffle_xor for gpu_warp_shuffle_xor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_shuffle_xor for gpu_warp_shuffle_xor")
val func = make_opencl_subgroup_kernel("sg_shuffle_xor_kernel", 106, warp_shuffle_xor_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_shuffle_xor(")
```

</details>

#### emits sub_group_ballot for gpu_warp_ballot

- emits sub_group_ballot for gpu_warp_ballot


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_ballot for gpu_warp_ballot")
val func = make_opencl_subgroup_kernel("sg_ballot_kernel", 107, warp_ballot_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_ballot(")
```

</details>

#### emits sub_group_barrier for Subgroup scope GpuBarrier

- emits sub_group_barrier for Subgroup scope GpuBarrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_barrier for Subgroup scope GpuBarrier")
val func = make_opencl_subgroup_kernel("sg_barrier_kernel", 108, subgroup_barrier_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_barrier(")
```

</details>

#### does not emit placeholder comment for any subgroup intrinsic

- does not emit placeholder comment for any subgroup intrinsic
   - Expected: source does not contain `subgroup barrier deferred`
   - Expected: source does not contain `// unsupported OpenCL intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit placeholder comment for any subgroup intrinsic")
val func = make_opencl_subgroup_kernel("sg_lane_id_check_kernel", 109, lane_id_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source.contains("subgroup barrier deferred")).to_equal(false)
expect(source.contains("// unsupported OpenCL intrinsic")).to_equal(false)
```

</details>

### subgroup intrinsics contract — CUDA/PTX backend

#### emits %laneid mov for gpu_lane_id

- emits %laneid mov for gpu_lane_id
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits %laneid mov for gpu_lane_id")
val func = make_cuda_subgroup_kernel("cuda_lane_id_kernel", 200, lane_id_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("%laneid")
```

</details>

#### emits %warpid mov for gpu_warp_id

- emits %warpid mov for gpu_warp_id
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits %warpid mov for gpu_warp_id")
val func = make_cuda_subgroup_kernel("cuda_warp_id_kernel", 201, warp_id_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("%warpid")
```

</details>

#### emits %WARP_SZ mov for gpu_warp_size

- emits %WARP_SZ mov for gpu_warp_size
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits %WARP_SZ mov for gpu_warp_size")
val func = make_cuda_subgroup_kernel("cuda_warp_size_kernel", 202, warp_size_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("%WARP_SZ")
```

</details>

#### emits shfl.sync.idx.b32 for gpu_warp_shuffle

- emits shfl.sync.idx.b32 for gpu_warp_shuffle
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.idx.b32 for gpu_warp_shuffle")
val func = make_cuda_subgroup_kernel("cuda_shuffle_kernel", 203, warp_shuffle_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.idx.b32")
```

</details>

#### emits shfl.sync.down.b32 for gpu_warp_shuffle_down

- emits shfl.sync.down.b32 for gpu_warp_shuffle_down
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.down.b32 for gpu_warp_shuffle_down")
val func = make_cuda_subgroup_kernel("cuda_shuffle_down_kernel", 204, warp_shuffle_down_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.down.b32")
```

</details>

#### emits shfl.sync.up.b32 for gpu_warp_shuffle_up

- emits shfl.sync.up.b32 for gpu_warp_shuffle_up
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.up.b32 for gpu_warp_shuffle_up")
val func = make_cuda_subgroup_kernel("cuda_shuffle_up_kernel", 205, warp_shuffle_up_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.up.b32")
```

</details>

#### emits shfl.sync.bfly.b32 for gpu_warp_shuffle_xor

- emits shfl.sync.bfly.b32 for gpu_warp_shuffle_xor
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.bfly.b32 for gpu_warp_shuffle_xor")
val func = make_cuda_subgroup_kernel("cuda_shuffle_xor_kernel", 206, warp_shuffle_xor_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.bfly.b32")
```

</details>

#### emits vote.sync.ballot.b32 for gpu_warp_ballot

- emits vote.sync.ballot.b32 for gpu_warp_ballot
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits vote.sync.ballot.b32 for gpu_warp_ballot")
val func = make_cuda_subgroup_kernel("cuda_ballot_kernel", 207, warp_ballot_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("vote.sync.ballot.b32")
```

</details>

#### emits bar.warp.sync for Subgroup scope GpuBarrier

- emits bar.warp.sync for Subgroup scope GpuBarrier
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits bar.warp.sync for Subgroup scope GpuBarrier")
val func = make_cuda_subgroup_kernel("cuda_subgroup_barrier_kernel", 208, subgroup_barrier_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("bar.warp.sync")
```

</details>

#### does not emit placeholder warp sync comment

- does not emit placeholder warp sync comment
   - Expected: result.is_ok() is true
   - Expected: ptx does not contain `// warp sync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit placeholder warp sync comment")
val func = make_cuda_subgroup_kernel("cuda_barrier_no_comment_kernel", 209, subgroup_barrier_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx.contains("// warp sync")).to_equal(false)
```

</details>

### gpu_intrinsics — subgroup recognition and arity

#### recognizes all subgroup intrinsic names

- recognizes all subgroup intrinsic names
   - Expected: recognize_gpu_intrinsic("gpu_lane_id") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_id") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_size") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_shuffle") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_shuffle_down") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_shuffle_up") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_shuffle_xor") != nil is true
   - Expected: recognize_gpu_intrinsic("gpu_warp_ballot") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes all subgroup intrinsic names")
expect(recognize_gpu_intrinsic("gpu_lane_id") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_id") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_size") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_shuffle") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_shuffle_down") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_shuffle_up") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_shuffle_xor") != nil).to_equal(true)
expect(recognize_gpu_intrinsic("gpu_warp_ballot") != nil).to_equal(true)
```

</details>

#### returns nil for unrecognized names

- returns nil for unrecognized names


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for unrecognized names")
expect(recognize_gpu_intrinsic("gpu_lane_id_nonexistent")).to_be_nil()
```

</details>

#### all_gpu_intrinsic_names includes subgroup intrinsics

- all_gpu_intrinsic_names includes subgroup intrinsics
   - Expected: names contains `gpu_lane_id`
   - Expected: names contains `gpu_warp_shuffle`
   - Expected: names contains `gpu_warp_ballot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("all_gpu_intrinsic_names includes subgroup intrinsics")
val names = all_gpu_intrinsic_names()
expect(names.contains("gpu_lane_id")).to_equal(true)
expect(names.contains("gpu_warp_shuffle")).to_equal(true)
expect(names.contains("gpu_warp_ballot")).to_equal(true)
```

</details>

#### gpu_lane_id is whitelisted as kernel builtin by gpu_checker

- gpu_lane_id is whitelisted as kernel builtin by gpu_checker
   - Expected: is_gpu_builtin_call("gpu_lane_id") is true
   - Expected: is_gpu_builtin_call("gpu_warp_shuffle") is true
   - Expected: is_gpu_builtin_call("gpu_warp_ballot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gpu_lane_id is whitelisted as kernel builtin by gpu_checker")
expect(is_gpu_builtin_call("gpu_lane_id")).to_equal(true)
expect(is_gpu_builtin_call("gpu_warp_shuffle")).to_equal(true)
expect(is_gpu_builtin_call("gpu_warp_ballot")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering subgroup intrinsics contract — OpenCL backend, subgroup intrinsics contract — CUDA/PTX backend, gpu_intrinsics — subgroup recognition and arity.
- subgroup intrinsics contract — OpenCL backend
- subgroup intrinsics contract — CUDA/PTX backend
- gpu_intrinsics — subgroup recognition and arity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b543f437c73af387344a882d6605064703fdc7ca6076e8ab4e9c3e1ed9a6835b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b543f437c73af387344a882d6605064703fdc7ca6076e8ab4e9c3e1ed9a6835b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b543f437c73af387344a882d6605064703fdc7ca6076e8ab4e9c3e1ed9a6835b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits get_sub_group_local_id() for gpu_lane_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits get_sub_group_id() for gpu_warp_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits get_sub_group_size() for gpu_warp_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
