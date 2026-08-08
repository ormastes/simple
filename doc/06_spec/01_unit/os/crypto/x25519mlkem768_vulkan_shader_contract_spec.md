# X25519mlkem768 Vulkan Shader Contract Specification

> Tests covering X25519MLKEM768 Vulkan NTT shader contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Vulkan Shader Contract Specification

## Scenarios

### X25519MLKEM768 Vulkan NTT shader contract

#### should use ping-pong workgroup storage and an explicit zeta buffer

- Inspect the forward shader storage and zeta-table contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the forward shader storage and zeta-table contract")
val shader = rt_file_read_text(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp") ?? ""
expect(shader).to_contain("layout(set = 0, binding = 2, std430) readonly buffer ZetaTable")
expect(shader).to_contain("shared int stage_a[256]")
expect(shader).to_contain("shared int stage_b[256]")
expect(shader).to_contain("if (tid < 128u)")
expect(shader).to_contain("stage_b[lower_tid] = next_lower")
expect(shader).to_contain("stage_b[upper_tid] = next_upper")
expect(shader).to_contain("stage_a[lower_tid] = next_lower")
expect(shader).to_contain("stage_a[upper_tid] = next_upper")
expect(shader).to_contain("memoryBarrierShared()")
expect(shader).to_contain("barrier()")
expect(shader.contains("stage_b[tid] = next_value")).to_be(false)
expect(shader.contains("const int zetas[128]")).to_be(false)
expect(shader).to_contain("int magnitude = -(value + 1)")
expect(shader).to_contain("((magnitude % 3329) + 1) % 3329")
expect(shader.contains("int reduced = value % 3329")).to_be(false)
```

</details>

#### should keep all stage barriers uniform and expose bounded diagnostics

- Inspect stage bounds and uniform shared-memory barrier ordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect stage bounds and uniform shared-memory barrier ordering")
val shader = rt_file_read_text(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp") ?? ""
expect(shader).to_contain("uint stage_count")
expect(shader).to_contain("min(parameters.stage_count, 7u)")
expect(shader).to_contain("stage < stages")
expect(shader).to_contain("uint len = 128u >> stage")
expect(shader).to_contain("uint zeta_base = 1u << stage")
val barrier = shader.index_of("memoryBarrierShared()")
val conditional_write = shader.index_of("if (current_is_a)")
expect(barrier).to_be_greater_than(conditional_write)
```

</details>

#### should bind the probe to the same three-buffer and seven-stage ABI

- Compare the native probe bindings with the shader stage ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the native probe bindings with the shader stage ABI")
val probe = rt_file_read_text(
    "test/fixtures/crypto/x25519mlkem768/vulkan_ntt_probe.c") ?? ""
expect(probe).to_contain("VkDescriptorSetLayoutBinding bindings[3]")
expect(probe).to_contain("VkDescriptorBufferInfo buffer_infos[3]")
expect(probe).to_contain("Parameters parameters = {BATCH, stage_count}")
expect(probe).to_contain("scalar_ntt(&expected[p * N], stage_count)")
expect(probe).to_contain("[stage-count:1..7]")
expect(probe).to_contain("requested_stages > 7")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Vulkan NTT shader contract.
- X25519MLKEM768 Vulkan NTT shader contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
