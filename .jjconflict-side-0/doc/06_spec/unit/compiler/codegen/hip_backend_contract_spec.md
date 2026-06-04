# Hip Backend Contract Specification

> <details>

<!-- sdn-diagram:id=hip_backend_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hip_backend_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hip_backend_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hip_backend_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hip Backend Contract Specification

## Scenarios

### HIP backend contract

#### names the HIP backend and supports HSACO artifact targets only

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = HipBackend.create(compileoptions_default_options())

expect(backend.backend_name()).to_equal("hip")
expect(backend.supports_target(CodegenTarget.HipHsaco)).to_equal(true)
expect(backend.supports_target(CodegenTarget.CudaPtx)).to_equal(false)
expect(backend.supports_target(CodegenTarget.OpenClC)).to_equal(false)
expect(backend.output_kind() == CodegenOutputKind.GpuCode).to_equal(true)
```

</details>

#### builds generated Engine2D HIP C++ to HSACO artifact evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### rejects incomplete HIP generated artifact evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32"
val contract = hip_backend_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", exported, 4096)

expect(contract.ready).to_equal(false)
expect(contract.status).to_equal("missing-entry-symbol:simple_2d_scroll_u32")
expect(contract.diagnostic).to_contain("HIP artifact rejected")
```

</details>

#### keeps generic MIR lowering honest until the HIP MIR emitter lands

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HIP backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
