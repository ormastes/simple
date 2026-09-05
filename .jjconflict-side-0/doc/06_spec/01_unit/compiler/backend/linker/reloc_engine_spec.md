# Reloc Engine Specification

> Tests covering reloc_engine - byte patch helpers, reloc_engine - reloc_arch_from_machine, reloc_engine - x86_64 relocations, reloc_engine - AArch64 relocations, reloc_engine - RISC-V relocations, reloc_engine - unified dispatch, reloc_engine - byte patching integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reloc Engine Specification

## Scenarios

### reloc_engine - byte patch helpers

#### patch_u32_le writes correct little-endian bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- patch_u32_le writes correct little-endian bytes
   - Expected: result[0] equals `0x78`
   - Expected: result[1] equals `0x56`
   - Expected: result[2] equals `0x34`
   - Expected: result[3] equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("patch_u32_le writes correct little-endian bytes")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = patch_u32_le(bytes, 0, 0x12345678)
expect(result[0]).to_equal(0x78)
expect(result[1]).to_equal(0x56)
expect(result[2]).to_equal(0x34)
expect(result[3]).to_equal(0x12)
```

</details>

#### patch_u64_le writes correct little-endian bytes

- patch_u64_le writes correct little-endian bytes
   - Expected: result[0] equals `0x08`
   - Expected: result[1] equals `0x07`
   - Expected: result[2] equals `0x06`
   - Expected: result[3] equals `0x05`
   - Expected: result[4] equals `0x04`
   - Expected: result[5] equals `0x03`
   - Expected: result[6] equals `0x02`
   - Expected: result[7] equals `0x01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("patch_u64_le writes correct little-endian bytes")
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

- read_u32_le reads back correct little-endian value
   - Expected: value equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("read_u32_le reads back correct little-endian value")
val bytes: [i64] = [0x78, 0x56, 0x34, 0x12]
val value = read_u32_le(bytes, 0)
expect(value).to_equal(0x12345678)
```

</details>

#### patch_u32_le then read_u32_le round-trips correctly

- patch_u32_le then read_u32_le round-trips correctly
   - Expected: read_back equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("patch_u32_le then read_u32_le round-trips correctly")
val bytes: [i64] = [0, 0, 0, 0]
val written = patch_u32_le(bytes, 0, 0xDEADBEEF)
val read_back = read_u32_le(written, 0)
expect(read_back).to_equal(0xDEADBEEF)
```

</details>

### reloc_engine - reloc_arch_from_machine

#### machine 62 maps to X86_64

- machine 62 maps to X86_64
   - Expected: arch equals `RelocArch.X86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("machine 62 maps to X86_64")
val arch = reloc_arch_from_machine(62)
expect(arch).to_equal(RelocArch.X86_64)
```

</details>

#### machine 183 maps to AArch64

- machine 183 maps to AArch64
   - Expected: arch equals `RelocArch.AArch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("machine 183 maps to AArch64")
val arch = reloc_arch_from_machine(183)
expect(arch).to_equal(RelocArch.AArch64)
```

</details>

#### machine 243 maps to Riscv64

- machine 243 maps to Riscv64
   - Expected: arch equals `RelocArch.Riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("machine 243 maps to Riscv64")
val arch = reloc_arch_from_machine(243)
expect(arch).to_equal(RelocArch.Riscv64)
```

</details>

### reloc_engine - x86_64 relocations

#### R_X86_64_NONE returns success with value 0

- R_X86_64_NONE returns success with value 0
   - Expected: result.success is true
   - Expected: result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_NONE returns success with value 0")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0)
```

</details>

#### R_X86_64_64 computes S + A

- R_X86_64_64 computes S + A
   - Expected: result.success is true
   - Expected: result.value equals `0x1008`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_64 computes S + A")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_64, 0x1000, 8, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1008)
```

</details>

#### R_X86_64_PC32 computes S + A - P

- R_X86_64_PC32 computes S + A - P
   - Expected: result.success is true
   - Expected: result.value equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_PC32 computes S + A - P")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_PC32, 0x2000, 0, 0x1000)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1000)
```

</details>

#### R_X86_64_PLT32 computes S + A - P

- R_X86_64_PLT32 computes S + A - P
   - Expected: result.success is true
   - Expected: result.value equals `0x1FF8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_PLT32 computes S + A - P")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_PLT32, 0x3000, -4, 0x1004)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x1FF8)
```

</details>

#### R_X86_64_32 computes S + A truncated to u32

- R_X86_64_32 computes S + A truncated to u32
   - Expected: result.success is true
   - Expected: result.value equals `0x400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_32 computes S + A truncated to u32")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_32, 0x400, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### R_X86_64_32S computes S + A

- R_X86_64_32S computes S + A
   - Expected: result.success is true
   - Expected: result.value equals `0x400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_32S computes S + A")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, R_X86_64_32S, 0x400, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### unsupported x86_64 reloc type returns failure with non-empty error

- unsupported x86_64 reloc type returns failure with non-empty error
   - Expected: result.success is false
   - Expected: result.error.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsupported x86_64 reloc type returns failure with non-empty error")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_x86_64(bytes, 0, 999, 0, 0, 0)
expect(result.success).to_equal(false)
expect(result.error.len() > 0).to_equal(true)
```

</details>

### reloc_engine - AArch64 relocations

#### R_AARCH64_NONE returns success with value 0

- R_AARCH64_NONE returns success with value 0
   - Expected: result.success is true
   - Expected: result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_AARCH64_NONE returns success with value 0")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0)
```

</details>

#### R_AARCH64_ABS64 computes S + A

- R_AARCH64_ABS64 computes S + A
   - Expected: result.success is true
   - Expected: result.value equals `0x10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_AARCH64_ABS64 computes S + A")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x10000)
```

</details>

#### R_AARCH64_CALL26 computes (S + A - P) >> 2 masked to 26 bits

- R_AARCH64_CALL26 computes (S + A - P) >> 2 masked to 26 bits
   - Expected: result.success is true
   - Expected: result.value equals `0x400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_AARCH64_CALL26 computes (S + A - P) >> 2 masked to 26 bits")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, R_AARCH64_CALL26, 0x2000, 0, 0x1000)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x400)
```

</details>

#### unsupported AArch64 reloc type returns failure with non-empty error

- unsupported AArch64 reloc type returns failure with non-empty error
   - Expected: result.success is false
   - Expected: result.error.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsupported AArch64 reloc type returns failure with non-empty error")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_aarch64(bytes, 0, 999, 0, 0, 0)
expect(result.success).to_equal(false)
expect(result.error.len() > 0).to_equal(true)
```

</details>

### reloc_engine - RISC-V relocations

#### R_RISCV_NONE returns success

- R_RISCV_NONE returns success
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_RISCV_NONE returns success")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_NONE, 0, 0, 0)
expect(result.success).to_equal(true)
```

</details>

#### R_RISCV_64 computes S + A

- R_RISCV_64 computes S + A
   - Expected: result.success is true
   - Expected: result.value equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_RISCV_64 computes S + A")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_64, 0x80000000, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x80000000)
```

</details>

#### R_RISCV_HI20 computes (S + A + 0x800) >> 12

- R_RISCV_HI20 computes (S + A + 0x800) >> 12
   - Expected: result.success is true
   - Expected: result.value equals `0x12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_RISCV_HI20 computes (S + A + 0x800) >> 12")
# 0x12345678 + 0x800 = 0x12345E78, >> 12 = 0x12345
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_HI20, 0x12345678, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x12345)
```

</details>

#### R_RISCV_LO12_I computes S + A masked to 12 bits

- R_RISCV_LO12_I computes S + A masked to 12 bits
   - Expected: result.success is true
   - Expected: result.value equals `0x678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_RISCV_LO12_I computes S + A masked to 12 bits")
val bytes: [i64] = [0, 0, 0, 0]
val result = reloc_apply_riscv(bytes, 0, R_RISCV_LO12_I, 0x12345678, 0, 0)
expect(result.success).to_equal(true)
expect(result.value).to_equal(0x678)
```

</details>

### reloc_engine - unified dispatch

#### reloc_apply with X86_64 arch matches reloc_apply_x86_64

- reloc_apply with X86_64 arch matches reloc_apply_x86_64
   - Expected: unified.success equals `direct.success`
   - Expected: unified.value equals `direct.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reloc_apply with X86_64 arch matches reloc_apply_x86_64")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val direct = reloc_apply_x86_64(bytes, 0, R_X86_64_64, 0x1000, 8, 0)
val unified = reloc_apply(RelocArch.X86_64, bytes, 0, R_X86_64_64, 0x1000, 8, 0)
expect(unified.success).to_equal(direct.success)
expect(unified.value).to_equal(direct.value)
```

</details>

#### reloc_apply with AArch64 arch matches reloc_apply_aarch64

- reloc_apply with AArch64 arch matches reloc_apply_aarch64
   - Expected: unified.success equals `direct.success`
   - Expected: unified.value equals `direct.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reloc_apply with AArch64 arch matches reloc_apply_aarch64")
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
val direct = reloc_apply_aarch64(bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
val unified = reloc_apply(RelocArch.AArch64, bytes, 0, R_AARCH64_ABS64, 0x10000, 0, 0)
expect(unified.success).to_equal(direct.success)
expect(unified.value).to_equal(direct.value)
```

</details>

### reloc_engine - byte patching integration

#### R_X86_64_64 reloc value patched as 8 LE bytes at offset

- R_X86_64_64 reloc value patched as 8 LE bytes at offset
   - Expected: result.success is true
   - Expected: result.value equals `0x1008`
   - Expected: patched[0] equals `0x08`
   - Expected: patched[1] equals `0x10`
   - Expected: patched[2] equals `0x00`
   - Expected: patched[3] equals `0x00`
   - Expected: patched[4] equals `0x00`
   - Expected: patched[5] equals `0x00`
   - Expected: patched[6] equals `0x00`
   - Expected: patched[7] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_64 reloc value patched as 8 LE bytes at offset")
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

- R_X86_64_PC32 reloc value patched as 4 LE bytes at offset
   - Expected: result.success is true
   - Expected: result.value equals `0x1000`
   - Expected: patched[0] equals `0x00`
   - Expected: patched[1] equals `0x10`
   - Expected: patched[2] equals `0x00`
   - Expected: patched[3] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("R_X86_64_PC32 reloc value patched as 4 LE bytes at offset")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering reloc_engine - byte patch helpers, reloc_engine - reloc_arch_from_machine, reloc_engine - x86_64 relocations, reloc_engine - AArch64 relocations, reloc_engine - RISC-V relocations, reloc_engine - unified dispatch, reloc_engine - byte patching integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d65e7e7e3bb8dd1a494ae4232cf487189c0c3e5de95a852c25f0fb4172231a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d65e7e7e3bb8dd1a494ae4232cf487189c0c3e5de95a852c25f0fb4172231a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d65e7e7e3bb8dd1a494ae4232cf487189c0c3e5de95a852c25f0fb4172231a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/linker/reloc_engine_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/linker/reloc_engine_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/linker/reloc_engine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/linker/reloc_engine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/linker/reloc_engine_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/linker/reloc_engine_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'patch_u32_le writes correct little-endian bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/linker/reloc_engine_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'patch_u64_le writes correct little-endian bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/linker/reloc_engine_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_u32_le reads back correct little-endian value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
