# Vec Types Contract Specification

> Tests covering vec_types — gpu_intrinsics recognition, vec_types contract — OpenCL backend vec4 load, vec_types contract — OpenCL backend vec4 store, vec_types contract — OpenCL backend vec2 load/store, vec_types contract — CUDA backend vec4 load, vec_types contract — CUDA backend vec4 store, vec_types contract — CUDA backend vec2 load, vec_types contract — CUDA backend vec2 store.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vec Types Contract Specification

## Scenarios

### vec_types — gpu_intrinsics recognition

#### recognizes gpu_vec4_load_f32 as a GPU intrinsic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes gpu_vec4_load_f32 as a GPU intrinsic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes gpu_vec4_load_f32 as a GPU intrinsic")
assert_true(is_gpu_intrinsic("gpu_vec4_load_f32"))
```

</details>

#### recognizes gpu_vec4_store_f32 as a GPU intrinsic

- recognizes gpu_vec4_store_f32 as a GPU intrinsic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes gpu_vec4_store_f32 as a GPU intrinsic")
assert_true(is_gpu_intrinsic("gpu_vec4_store_f32"))
```

</details>

#### recognizes gpu_vec2_load_f32 as a GPU intrinsic

- recognizes gpu_vec2_load_f32 as a GPU intrinsic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes gpu_vec2_load_f32 as a GPU intrinsic")
assert_true(is_gpu_intrinsic("gpu_vec2_load_f32"))
```

</details>

#### recognizes gpu_vec2_store_f32 as a GPU intrinsic

- recognizes gpu_vec2_store_f32 as a GPU intrinsic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes gpu_vec2_store_f32 as a GPU intrinsic")
assert_true(is_gpu_intrinsic("gpu_vec2_store_f32"))
```

</details>

#### rejects ordinary function names as GPU intrinsics

- rejects ordinary function names as GPU intrinsics


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ordinary function names as GPU intrinsics")
assert_true(not is_gpu_intrinsic("third"))
```

</details>

#### all_gpu_intrinsic_names includes gpu_vec4_load_f32

- all_gpu_intrinsic_names includes gpu_vec4_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_gpu_intrinsic_names includes gpu_vec4_load_f32")
val names = all_gpu_intrinsic_names()
val found = names.contains("gpu_vec4_load_f32")
assert_true(found)
```

</details>

#### all_gpu_intrinsic_names includes gpu_vec4_store_f32

- all_gpu_intrinsic_names includes gpu_vec4_store_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_gpu_intrinsic_names includes gpu_vec4_store_f32")
val names = all_gpu_intrinsic_names()
val found = names.contains("gpu_vec4_store_f32")
assert_true(found)
```

</details>

#### all_gpu_intrinsic_names includes gpu_vec2_load_f32

- all_gpu_intrinsic_names includes gpu_vec2_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_gpu_intrinsic_names includes gpu_vec2_load_f32")
val names = all_gpu_intrinsic_names()
val found = names.contains("gpu_vec2_load_f32")
assert_true(found)
```

</details>

#### all_gpu_intrinsic_names includes gpu_vec2_store_f32

- all_gpu_intrinsic_names includes gpu_vec2_store_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_gpu_intrinsic_names includes gpu_vec2_store_f32")
val names = all_gpu_intrinsic_names()
val found = names.contains("gpu_vec2_store_f32")
assert_true(found)
```

</details>

### vec_types contract — OpenCL backend vec4 load

#### emits vload4 for gpu_vec4_load_f32

- emits vload4 for gpu_vec4_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits vload4 for gpu_vec4_load_f32")
val func = make_opencl_vec_kernel("opencl_vec4_load", 300, vec4_load_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("vload4")
```

</details>

#### emits float4 type for gpu_vec4_load_f32

- emits float4 type for gpu_vec4_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits float4 type for gpu_vec4_load_f32")
val func = make_opencl_vec_kernel("opencl_vec4_load_ty", 301, vec4_load_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("float4")
```

</details>

#### emits diagnostic comment for gpu_vec4_load_f32 with bad arity

- emits diagnostic comment for gpu_vec4_load_f32 with bad arity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits diagnostic comment for gpu_vec4_load_f32 with bad arity")
val func = make_opencl_vec_kernel("opencl_vec4_load_bad", 302, vec4_load_bad_args_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("gpu_vec4_load_f32")
```

</details>

### vec_types contract — OpenCL backend vec4 store

#### emits vstore4 for gpu_vec4_store_f32

- emits vstore4 for gpu_vec4_store_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits vstore4 for gpu_vec4_store_f32")
val func = make_opencl_vec_kernel("opencl_vec4_store", 310, vec4_store_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("vstore4")
```

</details>

#### emits diagnostic comment for gpu_vec4_store_f32 with bad arity

- emits diagnostic comment for gpu_vec4_store_f32 with bad arity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits diagnostic comment for gpu_vec4_store_f32 with bad arity")
val func = make_opencl_vec_kernel("opencl_vec4_store_bad", 311, vec4_store_bad_args_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("gpu_vec4_store_f32")
```

</details>

### vec_types contract — OpenCL backend vec2 load/store

#### emits vload2 for gpu_vec2_load_f32

- emits vload2 for gpu_vec2_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits vload2 for gpu_vec2_load_f32")
val func = make_opencl_vec_kernel("opencl_vec2_load", 320, vec2_load_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("vload2")
```

</details>

#### emits float2 type for gpu_vec2_load_f32

- emits float2 type for gpu_vec2_load_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits float2 type for gpu_vec2_load_f32")
val func = make_opencl_vec_kernel("opencl_vec2_load_ty", 321, vec2_load_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("float2")
```

</details>

#### emits vstore2 for gpu_vec2_store_f32

- emits vstore2 for gpu_vec2_store_f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits vstore2 for gpu_vec2_store_f32")
val func = make_opencl_vec_kernel("opencl_vec2_store", 322, vec2_store_block())
val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
expect(source).to_contain("vstore2")
```

</details>

### vec_types contract — CUDA backend vec4 load

#### rejects gpu_vec4_load_f32 until MIR carries vector results

- rejects gpu_vec4_load_f32 until MIR carries vector results
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects gpu_vec4_load_f32 until MIR carries vector results")
val func = make_cuda_vec_kernel("cuda_vec4_load", 400, vec4_load_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("vector loads require MIR vector result lowering")
```

</details>

#### rejects gpu_vec4_load_f32 with bad arity

- rejects gpu_vec4_load_f32 with bad arity
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects gpu_vec4_load_f32 with bad arity")
val func = make_cuda_vec_kernel("cuda_vec4_load_bad", 401, vec4_load_bad_args_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("requires exactly 2 arguments")
```

</details>

### vec_types contract — CUDA backend vec4 store

#### emits st.global.v4.f32 for gpu_vec4_store_f32

- emits st.global.v4.f32 for gpu_vec4_store_f32
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits st.global.v4.f32 for gpu_vec4_store_f32")
val func = make_cuda_vec_kernel("cuda_vec4_store", 410, vec4_store_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("st.global.v4.f32")
```

</details>

#### rejects gpu_vec4_store_f32 with bad arity

- rejects gpu_vec4_store_f32 with bad arity
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects gpu_vec4_store_f32 with bad arity")
val func = make_cuda_vec_kernel("cuda_vec4_store_bad", 411, vec4_store_bad_args_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("requires exactly 6 arguments")
```

</details>

### vec_types contract — CUDA backend vec2 load

#### rejects gpu_vec2_load_f32 until MIR carries vector results

- rejects gpu_vec2_load_f32 until MIR carries vector results
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects gpu_vec2_load_f32 until MIR carries vector results")
val func = make_cuda_vec_kernel("cuda_vec2_load", 420, vec2_load_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("vector loads require MIR vector result lowering")
```

</details>

### vec_types contract — CUDA backend vec2 store

#### emits st.global.v2.f32 for gpu_vec2_store_f32

- emits st.global.v2.f32 for gpu_vec2_store_f32
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits st.global.v2.f32 for gpu_vec2_store_f32")
val func = make_cuda_vec_kernel("cuda_vec2_store", 430, vec2_store_block())
val backend = CudaBackend.create((8, 6))
val result = backend.compile(make_module_from(func))
expect(result.is_ok()).to_equal(true)
val ptx = result.unwrap().ptx
expect(ptx).to_contain("st.global.v2.f32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/vec_types_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering vec_types — gpu_intrinsics recognition, vec_types contract — OpenCL backend vec4 load, vec_types contract — OpenCL backend vec4 store, vec_types contract — OpenCL backend vec2 load/store, vec_types contract — CUDA backend vec4 load, vec_types contract — CUDA backend vec4 store, vec_types contract — CUDA backend vec2 load, vec_types contract — CUDA backend vec2 store.
- vec_types — gpu_intrinsics recognition
- vec_types contract — OpenCL backend vec4 load
- vec_types contract — OpenCL backend vec4 store
- vec_types contract — OpenCL backend vec2 load/store
- vec_types contract — CUDA backend vec4 load
- vec_types contract — CUDA backend vec4 store
- vec_types contract — CUDA backend vec2 load
- vec_types contract — CUDA backend vec2 store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `9a3aef808a348813af8614b4fea70148228a5aa6bff4c1d85aa03661796b14d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a3aef808a348813af8614b4fea70148228a5aa6bff4c1d85aa03661796b14d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a3aef808a348813af8614b4fea70148228a5aa6bff4c1d85aa03661796b14d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/vec_types_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/vec_types_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/vec_types_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/vec_types_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/vec_types_contract_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes gpu_vec4_load_f32 as a GPU intrinsic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vec_types_contract_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes gpu_vec4_store_f32 as a GPU intrinsic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vec_types_contract_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes gpu_vec2_load_f32 as a GPU intrinsic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
