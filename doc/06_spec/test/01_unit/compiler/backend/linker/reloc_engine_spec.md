# Reloc Engine Specification

> <details>

<!-- sdn-diagram:id=reloc_engine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reloc_engine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reloc_engine_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reloc_engine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reloc Engine Specification

## Scenarios

### reloc_engine - byte patch helpers

#### patch_u32_le writes correct little-endian bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = patch_u32_le(bytes, 0, 0x12345678)
expect(result[0]).to_equal(0x78)
expect(result[1]).to_equal(0x56)
expect(result[2]).to_equal(0x34)
expect(result[3]).to_equal(0x12)
```

</details>

#### patch_u64_le writes correct little-endian bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = patch_u64_le(bytes, 0, 0x0102030405060708)
expect(result[0]).to_equal(0x08)
expect(result[1]).to_equal(0x07)
expect(result[2]).to_equal(0x06)
expect(result[3]).to_equal(0x05)
expect(result[4]).to_equal(0x04)
expect(result[5]).to_equal(0x03)
expect(result[6]).to_equal(0x02)
expect(result[7]).to_equal(0x01)
```

</details>

#### read_u32_le reads back correct little-endian value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x78, 0x56, 0x34, 0x12]
val value = read_u32_le(bytes, 0)
expect(value).to_equal(0x12345678)
```

</details>

#### patch_u32_le then read_u32_le round-trips correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val written = patch_u32_le(bytes, 0, 0xDEADBEEF)
val read_back = read_u32_le(written, 0)
expect(read_back).to_equal(0xDEADBEEF)
```

</details>

### reloc_engine - reloc_arch_from_machine

#### machine 62 maps to X86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = reloc_arch_from_machine(62)
expect(arch == RelocArch.X86_64).to_equal(true)
```

</details>

#### machine 183 maps to AArch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = reloc_arch_from_machine(183)
expect(arch == RelocArch.AArch64).to_equal(true)
```

</details>

#### machine 243 maps to Riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = reloc_arch_from_machine(243)
expect(arch == RelocArch.Riscv64).to_equal(true)
```

</details>

### reloc_engine - x86_64 relocations

#### R_X86_64_NONE returns success with value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0)
```

</details>

#### R_X86_64_64 computes S + A

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_64, 0x1000, 8, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1008)
```

</details>

#### R_X86_64_PC32 computes S + A - P

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_PC32, 0x2000, 0, 0x1000)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1000)
```

</details>

#### R_X86_64_PLT32 computes S + A - P

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_PLT32, 0x3000, -4, 0x1004)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1FF8)
```

</details>

#### R_X86_64_32 computes S + A truncated to u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_32, 0x400, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### R_X86_64_32S computes S + A

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_32S, 0x400, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### unsupported x86_64 reloc type returns failure with non-empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, 999, 0, 0, 0)
expect(result.success).to_equal(false)
expect(result.error.len() > 0).to_equal(true)
```

</details>

### reloc_engine - AArch64 relocations

#### R_AARCH64_NONE returns success with value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0)
```

</details>

#### R_AARCH64_ABS64 computes S + A

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x10000)
```

</details>

#### R_AARCH64_CALL26 computes (S + A - P) >> 2 masked to 26 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_CALL26, 0x2000, 0, 0x1000)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### unsupported AArch64 reloc type returns failure with non-empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, 999, 0, 0, 0)
expect(result.success).to_equal(false)
expect(result.error.len() > 0).to_equal(true)
```

</details>

### reloc_engine - RISC-V relocations

#### R_RISCV_NONE returns success

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
```

</details>

#### R_RISCV_64 computes S + A

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_64, 0x80000000, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x80000000)
```

</details>

#### R_RISCV_HI20 computes (S + A + 0x800) >> 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x12345678 + 0x800 = 0x12345E78, >> 12 = 0x12345
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_HI20, 0x12345678, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x12345)
```

</details>

#### R_RISCV_LO12_I computes S + A masked to 12 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_LO12_I, 0x12345678, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x678)
```

</details>

### reloc_engine - unified dispatch

#### reloc_apply with X86_64 arch matches reloc_apply_x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val direct = reloc_apply_x86_64(bytes, 0, R_X86_64_64, 0x1000, 8, 0)
val unified = reloc_apply(RelocArch.X86_64, bytes, 0, R_X86_64_64, 0x1000, 8, 0)
expect(unified.success).to_equal(direct.success)
expect(unified.value).to_equal(direct.value)
```

</details>

#### reloc_apply with AArch64 arch matches reloc_apply_aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val direct = reloc_apply_aarch64(bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
val unified = reloc_apply(RelocArch.AArch64, bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
expect(unified.success).to_equal(direct.success)
expect(unified.value).to_equal(direct.value)
```

</details>

### reloc_engine - byte patching integration

#### R_X86_64_64 reloc value patched as 8 LE bytes at offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# reloc_patch_bytes internally uses .set() which requires compiled mode.
# Verify the same end-to-end semantics by composing reloc_apply + patch_u64_le.
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply(RelocArch.X86_64, bytes, 0, R_X86_64_64, 0x1000, 8, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1008)
val patched = patch_u64_le(bytes, 0, result.value)
# 0x1008 in LE: 0x08, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
expect(patched[0]).to_equal(0x08)
expect(patched[1]).to_equal(0x10)
expect(patched[2]).to_equal(0x00)
expect(patched[3]).to_equal(0x00)
expect(patched[4]).to_equal(0x00)
expect(patched[5]).to_equal(0x00)
expect(patched[6]).to_equal(0x00)
expect(patched[7]).to_equal(0x00)
```

</details>

#### R_X86_64_PC32 reloc value patched as 4 LE bytes at offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify end-to-end via reloc_apply + patch_u32_le (avoids interpreter .set() dispatch issue).
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply(RelocArch.X86_64, bytes, 0, R_X86_64_PC32, 0x2000, 0, 0x1000)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1000)
val patched = patch_u32_le(bytes, 0, result.value)
# 0x1000 in LE: 0x00, 0x10, 0x00, 0x00
expect(patched[0]).to_equal(0x00)
expect(patched[1]).to_equal(0x10)
expect(patched[2]).to_equal(0x00)
expect(patched[3]).to_equal(0x00)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/reloc_engine_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- reloc_engine - byte patch helpers
- reloc_engine - reloc_arch_from_machine
- reloc_engine - x86_64 relocations
- reloc_engine - AArch64 relocations
- reloc_engine - RISC-V relocations
- reloc_engine - unified dispatch
- reloc_engine - byte patching integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
