# Vulkan Cross Arch Specification

> <details>

<!-- sdn-diagram:id=vulkan_cross_arch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_cross_arch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_cross_arch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_cross_arch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Cross Arch Specification

## Scenarios

### VulkanCrossRenderer

#### creates for riscv64 with vulkan backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
expect(r.target).to_equal("riscv64")
expect(r.backend).to_equal("vulkan")
expect(r.target_bits).to_equal(64)
```

</details>

#### creates for riscv32 with scalar fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32()
expect(r.target).to_equal("riscv32")
expect(r.backend).to_equal("scalar")
expect(r.target_bits).to_equal(32)
```

</details>

#### creates for aarch64 with vulkan backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64()
expect(r.target).to_equal("aarch64")
expect(r.backend).to_equal("vulkan")
expect(r.target_bits).to_equal(64)
```

</details>

#### creates for arm32 with scalar fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32()
expect(r.target).to_equal("arm32")
expect(r.backend).to_equal("scalar")
expect(r.target_bits).to_equal(32)
```

</details>

#### riscv64 is_vulkan returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
expect(r.backend == "vulkan").to_equal(true)
```

</details>

#### riscv32 is_scalar returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32()
expect(r.backend == "scalar").to_equal(true)
```

</details>

#### aarch64 is_vulkan returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64()
expect(r.backend == "vulkan").to_equal(true)
```

</details>

#### arm32 is_scalar returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32()
expect(r.backend == "scalar").to_equal(true)
```

</details>

#### renderer starts uninitialized

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
expect(r.initialized == false).to_equal(true)
```

</details>

#### frame_count starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
expect(r.frame_count).to_equal(0)
```

</details>

#### riscv64 init_device returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
val err = r.init_device()
expect(err).to_equal("")
expect(r.initialized).to_equal(true)
```

</details>

#### riscv32 init_device returns diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32()
val err = r.init_device()
expect(err).to_equal("GPU unavailable on riscv32")
expect(r.initialized).to_equal(true)
```

</details>

#### aarch64 init_device returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64()
val err = r.init_device()
expect(err).to_equal("")
```

</details>

#### arm32 init_device returns diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32()
val err = r.init_device()
expect(err).to_equal("GLES preferred; scalar fallback in pure Simple layer")
expect(r.initialized).to_equal(true)
```

</details>

#### riscv64 qemu_system_cmd includes virtio-gpu-pci

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
val cmd = r.qemu_system_cmd()
expect(cmd).to_equal("qemu-system-riscv64 -M virt -device virtio-gpu-pci")
```

</details>

#### riscv32 qemu_system_cmd has no virtio-gpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32()
val cmd = r.qemu_system_cmd()
expect(cmd).to_equal("qemu-system-riscv32 -M virt")
```

</details>

#### aarch64 qemu_system_cmd includes virtio-gpu-pci

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64()
val cmd = r.qemu_system_cmd()
expect(cmd).to_equal("qemu-system-aarch64 -M virt -device virtio-gpu-pci")
```

</details>

#### arm32 qemu_system_cmd has no virtio-gpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32()
val cmd = r.qemu_system_cmd()
expect(cmd).to_equal("qemu-system-arm -M virt")
```

</details>

#### riscv64 present after init returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64_inited()
val fc = r.present()
expect(fc).to_equal(1)
```

</details>

#### riscv32 present after init returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32_inited()
val fc = r.present()
expect(fc).to_equal(1)
```

</details>

#### aarch64 present after init returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64_inited()
val fc = r.present()
expect(fc).to_equal(1)
```

</details>

#### arm32 present after init returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32_inited()
val fc = r.present()
expect(fc).to_equal(1)
```

</details>

#### frame_count increments each present call

1. r present
2. r present
   - Expected: fc equals `3`
   - Expected: r.frame_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64_inited()
r.present()
r.present()
val fc = r.present()
expect(fc).to_equal(3)
expect(r.frame_count).to_equal(3)
```

</details>

#### present before init returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
val fc = r.present()
expect(fc).to_equal(0)
expect(r.frame_count).to_equal(0)
```

</details>

#### riscv32 diagnostic is set before init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32()
expect(r.diagnostic).to_equal("GPU unavailable on riscv32")
```

</details>

#### arm32 diagnostic is set before init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_arm32()
expect(r.diagnostic).to_equal("GLES preferred; scalar fallback in pure Simple layer")
```

</details>

#### riscv64 diagnostic is empty (no fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64()
expect(r.diagnostic).to_equal("")
```

</details>

#### aarch64 diagnostic is empty (no fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_aarch64()
expect(r.diagnostic).to_equal("")
```

</details>

#### get_backend_info contains target name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64_inited()
val info = r.get_backend_info()
expect(info.contains("riscv64")).to_equal(true)
```

</details>

#### get_backend_info contains backend vulkan for rv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64_inited()
val info = r.get_backend_info()
expect(info.contains("vulkan")).to_equal(true)
```

</details>

#### get_backend_info contains scalar for rv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv32_inited()
val info = r.get_backend_info()
expect(info.contains("scalar")).to_equal(true)
```

</details>

#### get_backend_info shows initialized yes after init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_rv64_inited()
val info = r.get_backend_info()
expect(info.contains("initialized=yes")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/vulkan_cross_arch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VulkanCrossRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
