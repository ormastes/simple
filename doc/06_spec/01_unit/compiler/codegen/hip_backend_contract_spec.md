# Hip Backend Contract Specification

> Tests covering HIP backend contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hip Backend Contract Specification

## Scenarios

### HIP backend contract

#### names the HIP backend and supports HSACO artifact targets only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names the HIP backend and supports HSACO artifact targets only
   - Expected: backend.backend_name() equals `hip`
   - Expected: backend.supports_target(CodegenTarget.HipHsaco) is true
   - Expected: backend.supports_target(CodegenTarget.CudaPtx) is false
   - Expected: backend.supports_target(CodegenTarget.OpenClC) is false
   - Expected: backend.output_kind() equals `CodegenOutputKind.GpuCode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the HIP backend and supports HSACO artifact targets only")
val backend = HipBackend.create(compileoptions_default_options())

expect(backend.backend_name()).to_equal("hip")
expect(backend.supports_target(CodegenTarget.HipHsaco)).to_equal(true)
expect(backend.supports_target(CodegenTarget.CudaPtx)).to_equal(false)
expect(backend.supports_target(CodegenTarget.OpenClC)).to_equal(false)
expect(backend.output_kind()).to_equal(CodegenOutputKind.GpuCode)
```

</details>

#### builds generated Engine2D HIP C++ to HSACO artifact evidence

- builds generated Engine2D HIP C++ to HSACO artifact evidence
   - Expected: contract.ready is true
   - Expected: contract.status equals `compiled_artifact_verified`
   - Expected: contract.plan.source_format equals `hip-cpp`
   - Expected: contract.plan.binary_format equals `hsaco`
   - Expected: contract.plan.artifact_path_suffix equals `simple_2d_optimization.hsaco`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds generated Engine2D HIP C++ to HSACO artifact evidence")
val exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32"
val contract = hip_backend_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", exported, 4096)

expect(contract.ready).to_equal(true)
expect(contract.status).to_equal("compiled_artifact_verified")
expect(contract.plan.source_format).to_equal("hip-cpp")
expect(contract.plan.binary_format).to_equal("hsaco")
expect(contract.plan.artifact_path_suffix).to_equal("simple_2d_optimization.hsaco")
expect(contract.source).to_contain("extern \"C\" __global__ void simple_2d_fill_u32")
expect(contract.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(contract.summary()).to_contain("ready=true")
```

</details>

#### exposes one shared generated Engine2D contract for CUDA and HIP

- exposes one shared generated Engine2D contract for CUDA and HIP
   - Expected: cuda.backend_name equals `cuda`
   - Expected: cuda.ready is true
   - Expected: cuda.plan.source_format equals `cuda-c`
   - Expected: cuda.plan.binary_format equals `ptx`
   - Expected: hip.backend_name equals `hip`
   - Expected: hip.ready is true
   - Expected: hip.plan.source_format equals `hip-cpp`
   - Expected: hip.plan.binary_format equals `hsaco`
   - Expected: bad_cuda.ready is false
   - Expected: bad_cuda.status equals `artifact-magic-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes one shared generated Engine2D contract for CUDA and HIP")
val exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32"
val cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", exported, 4096)
val hip = hip_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", exported, 4096)
val bad_cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", exported, 4096)

expect(cuda.backend_name).to_equal("cuda")
expect(cuda.ready).to_equal(true)
expect(cuda.plan.source_format).to_equal("cuda-c")
expect(cuda.plan.binary_format).to_equal("ptx")
expect(cuda.source).to_contain("extern \"C\" __global__ void simple_2d_fill_u32")
expect(cuda.summary()).to_contain("backend=cuda")
expect(hip.backend_name).to_equal("hip")
expect(hip.ready).to_equal(true)
expect(hip.plan.source_format).to_equal("hip-cpp")
expect(hip.plan.binary_format).to_equal("hsaco")
expect(hip.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(bad_cuda.ready).to_equal(false)
expect(bad_cuda.status).to_equal("artifact-magic-mismatch")
expect(bad_cuda.diagnostic).to_contain("CUDA artifact rejected")
```

</details>

#### rejects incomplete HIP generated artifact evidence

- rejects incomplete HIP generated artifact evidence
   - Expected: contract.ready is false
   - Expected: contract.status equals `missing-entry-symbol:simple_2d_scroll_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incomplete HIP generated artifact evidence")
val exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32"
val contract = hip_backend_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", exported, 4096)

expect(contract.ready).to_equal(false)
expect(contract.status).to_equal("missing-entry-symbol:simple_2d_scroll_u32")
expect(contract.diagnostic).to_contain("HIP artifact rejected")
```

</details>

#### keeps generic MIR lowering honest until the HIP MIR emitter lands

- keeps generic MIR lowering honest until the HIP MIR emitter lands
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps generic MIR lowering honest until the HIP MIR emitter lands")
val backend = HipBackend.create(compileoptions_default_options())
val module = MirModule(name: "hip_generic_module", functions: {}, statics: {}, constants: {}, types: {})
val result = backend.compile_module(module)

expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("HIP MIR lowering is not implemented yet")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/hip_backend_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIP backend contract.
- HIP backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `fd01383c585a5af794bc8f9cd521ab83ca1fa6d834666458e519ef7474f346f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd01383c585a5af794bc8f9cd521ab83ca1fa6d834666458e519ef7474f346f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd01383c585a5af794bc8f9cd521ab83ca1fa6d834666458e519ef7474f346f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/hip_backend_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/hip_backend_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/hip_backend_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/hip_backend_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/hip_backend_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the HIP backend and supports HSACO artifact targets only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/hip_backend_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds generated Engine2D HIP C++ to HSACO artifact evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/hip_backend_contract_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes one shared generated Engine2D contract for CUDA and HIP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
