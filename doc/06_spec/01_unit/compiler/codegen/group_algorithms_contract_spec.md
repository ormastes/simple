# Group Algorithms Contract Specification

> Tests covering group algorithms contract — OpenCL backend, group algorithms contract — CUDA/PTX backend, group algorithms — recognition and arity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Group Algorithms Contract Specification

## Scenarios

### group algorithms contract — OpenCL backend

#### emits sub_group_reduce_add for gpu_warp_reduce_add

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits sub_group_reduce_add for gpu_warp_reduce_add


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_reduce_add for gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_reduce_add_kernel", 300, warp_reduce_add_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_reduce_add(")
```

</details>

#### emits sub_group_broadcast for gpu_warp_broadcast

- emits sub_group_broadcast for gpu_warp_broadcast


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_broadcast for gpu_warp_broadcast")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_broadcast_kernel", 301, warp_broadcast_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_broadcast(")
```

</details>

#### emits sub_group_scan_inclusive_add for gpu_warp_scan_add

- emits sub_group_scan_inclusive_add for gpu_warp_scan_add


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits sub_group_scan_inclusive_add for gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_scan_add_kernel", 302, warp_scan_add_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("sub_group_scan_inclusive_add(")
```

</details>

#### does not emit unsupported placeholder for reduce_add

- does not emit unsupported placeholder for reduce_add
   - Expected: source does not contain `// unsupported OpenCL intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit unsupported placeholder for reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_reduce_no_placeholder", 303, warp_reduce_add_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source.contains("// unsupported OpenCL intrinsic")).to_equal(false)
```

</details>

#### does not emit unsupported placeholder for broadcast

- does not emit unsupported placeholder for broadcast
   - Expected: source does not contain `// unsupported OpenCL intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit unsupported placeholder for broadcast")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_broadcast_no_placeholder", 304, warp_broadcast_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source.contains("// unsupported OpenCL intrinsic")).to_equal(false)
```

</details>

#### does not emit unsupported placeholder for scan_add

- does not emit unsupported placeholder for scan_add
   - Expected: source does not contain `// unsupported OpenCL intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit unsupported placeholder for scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_opencl_group_kernel("sg_scan_no_placeholder", 305, warp_scan_add_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source.contains("// unsupported OpenCL intrinsic")).to_equal(false)
```

</details>

### group algorithms contract — CUDA/PTX backend

#### emits shfl.sync.bfly.b32 for gpu_warp_reduce_add

- emits shfl.sync.bfly.b32 for gpu_warp_reduce_add
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.bfly.b32 for gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_reduce_add_kernel", 400, warp_reduce_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.bfly.b32")
```

</details>

#### emits exactly 5 shfl.sync.bfly.b32 steps for gpu_warp_reduce_add

- emits exactly 5 shfl.sync.bfly.b32 steps for gpu_warp_reduce_add
   - Expected: result.is_ok() is true
   - Expected: bfly_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits exactly 5 shfl.sync.bfly.b32 steps for gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_reduce_count_kernel", 401, warp_reduce_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
val bfly_count = count_occurrences(ptx, "shfl.sync.bfly.b32")
expect(bfly_count).to_equal(5)  # oracle: bfly_count must equal 5 — authoritative contract constant
```

</details>

#### emits add.s32 in reduce sequence for gpu_warp_reduce_add

- emits add.s32 in reduce sequence for gpu_warp_reduce_add
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits add.s32 in reduce sequence for gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_reduce_add_add_kernel", 402, warp_reduce_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("add.s32")
```

</details>

#### emits shfl.sync.idx.b32 for gpu_warp_broadcast

- emits shfl.sync.idx.b32 for gpu_warp_broadcast
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.idx.b32 for gpu_warp_broadcast")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_broadcast_kernel", 403, warp_broadcast_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.idx.b32")
```

</details>

#### emits shfl.sync.up.b32 for gpu_warp_scan_add

- emits shfl.sync.up.b32 for gpu_warp_scan_add
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits shfl.sync.up.b32 for gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_scan_add_kernel", 404, warp_scan_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("shfl.sync.up.b32")
```

</details>

#### emits exactly 5 shfl.sync.up.b32 steps for gpu_warp_scan_add

- emits exactly 5 shfl.sync.up.b32 steps for gpu_warp_scan_add
   - Expected: result.is_ok() is true
   - Expected: up_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits exactly 5 shfl.sync.up.b32 steps for gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_scan_count_kernel", 405, warp_scan_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
val up_count = count_occurrences(ptx, "shfl.sync.up.b32")
expect(up_count).to_equal(5)  # oracle: up_count must equal 5 — authoritative contract constant
```

</details>

#### emits setp.ge.u32 predicates for gpu_warp_scan_add

- emits setp.ge.u32 predicates for gpu_warp_scan_add
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits setp.ge.u32 predicates for gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_scan_setp_kernel", 406, warp_scan_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("setp.ge.u32")
```

</details>

#### does not emit Unknown intrinsic comment for gpu_warp_reduce_add

- does not emit Unknown intrinsic comment for gpu_warp_reduce_add
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().ptx does not contain `Unknown intrinsic: gpu_warp_reduce_add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit Unknown intrinsic comment for gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_reduce_no_unknown", 407, warp_reduce_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().ptx.contains("Unknown intrinsic: gpu_warp_reduce_add")).to_equal(false)
```

</details>

#### does not emit Unknown intrinsic comment for gpu_warp_broadcast

- does not emit Unknown intrinsic comment for gpu_warp_broadcast
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().ptx does not contain `Unknown intrinsic: gpu_warp_broadcast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit Unknown intrinsic comment for gpu_warp_broadcast")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_broadcast_no_unknown", 408, warp_broadcast_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().ptx.contains("Unknown intrinsic: gpu_warp_broadcast")).to_equal(false)
```

</details>

#### does not emit Unknown intrinsic comment for gpu_warp_scan_add

- does not emit Unknown intrinsic comment for gpu_warp_scan_add
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().ptx does not contain `Unknown intrinsic: gpu_warp_scan_add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not emit Unknown intrinsic comment for gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val func = make_cuda_group_kernel("cuda_scan_no_unknown", 409, warp_scan_add_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().ptx.contains("Unknown intrinsic: gpu_warp_scan_add")).to_equal(false)
```

</details>

### group algorithms — recognition and arity

#### recognizes gpu_warp_reduce_add

- recognizes gpu_warp_reduce_add
   - Expected: recognize_gpu_intrinsic("gpu_warp_reduce_add") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes gpu_warp_reduce_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(recognize_gpu_intrinsic("gpu_warp_reduce_add") != nil).to_equal(true)
```

</details>

#### recognizes gpu_warp_broadcast

- recognizes gpu_warp_broadcast
   - Expected: recognize_gpu_intrinsic("gpu_warp_broadcast") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes gpu_warp_broadcast")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(recognize_gpu_intrinsic("gpu_warp_broadcast") != nil).to_equal(true)
```

</details>

#### recognizes gpu_warp_scan_add

- recognizes gpu_warp_scan_add
   - Expected: recognize_gpu_intrinsic("gpu_warp_scan_add") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes gpu_warp_scan_add")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(recognize_gpu_intrinsic("gpu_warp_scan_add") != nil).to_equal(true)
```

</details>

#### all_gpu_intrinsic_names includes group algorithm intrinsics

- all_gpu_intrinsic_names includes group algorithm intrinsics
   - Expected: names contains `gpu_warp_reduce_add`
   - Expected: names contains `gpu_warp_broadcast`
   - Expected: names contains `gpu_warp_scan_add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("all_gpu_intrinsic_names includes group algorithm intrinsics")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val names = all_gpu_intrinsic_names()
expect(names.contains("gpu_warp_reduce_add")).to_equal(true)
expect(names.contains("gpu_warp_broadcast")).to_equal(true)
expect(names.contains("gpu_warp_scan_add")).to_equal(true)
```

</details>

#### group algorithm intrinsics are whitelisted by gpu_checker

- group algorithm intrinsics are whitelisted by gpu_checker
   - Expected: is_gpu_builtin_call("gpu_warp_reduce_add") is true
   - Expected: is_gpu_builtin_call("gpu_warp_broadcast") is true
   - Expected: is_gpu_builtin_call("gpu_warp_scan_add") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("group algorithm intrinsics are whitelisted by gpu_checker")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(is_gpu_builtin_call("gpu_warp_reduce_add")).to_equal(true)
expect(is_gpu_builtin_call("gpu_warp_broadcast")).to_equal(true)
expect(is_gpu_builtin_call("gpu_warp_scan_add")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/group_algorithms_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering group algorithms contract — OpenCL backend, group algorithms contract — CUDA/PTX backend, group algorithms — recognition and arity.
- group algorithms contract — OpenCL backend
- group algorithms contract — CUDA/PTX backend
- group algorithms — recognition and arity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `40ebf5160afbb368f14231ebcdf621411ce74ffa4ae463a72fb5a3b50fc48100`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40ebf5160afbb368f14231ebcdf621411ce74ffa4ae463a72fb5a3b50fc48100`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40ebf5160afbb368f14231ebcdf621411ce74ffa4ae463a72fb5a3b50fc48100`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/codegen/group_algorithms_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/group_algorithms_contract_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/codegen/group_algorithms_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/group_algorithms_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/group_algorithms_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
