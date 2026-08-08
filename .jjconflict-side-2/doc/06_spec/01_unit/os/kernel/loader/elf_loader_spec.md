# Elf Loader Specification

> <details>

<!-- sdn-diagram:id=elf_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf_loader_spec -> std
elf_loader_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Loader Specification

## Scenarios

### ELF loader

#### parses a minimal RV64 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_riscv_executable(make_rv64_exec(), Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf64)
expect(loaded.entry).to_equal(0x400000)
expect(loaded.segments.len()).to_equal(1)
expect(loaded.segments[0].file_offset).to_equal(0x1000)
```

</details>

#### parses a minimal RV32 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_riscv_executable(make_rv32_exec(), Architecture.Riscv32)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf32)
expect(loaded.entry).to_equal(0x80000000)
expect(loaded.segments.len()).to_equal(1)
expect(loaded.segments[0].virt_addr).to_equal(0x80000000)
```

</details>

#### rejects class mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_riscv_executable(make_rv32_exec(), Architecture.Riscv64)
expect(image.is_err()).to_equal(true)
```

</details>

#### rejects images without PT_LOAD

1. var bytes = make rv64 exec
2. bytes[64] = 0 to u8
   - Expected: image.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = make_rv64_exec()
bytes[64] = 0.to_u8()
val image = load_riscv_executable(bytes, Architecture.Riscv64)
expect(image.is_err()).to_equal(true)
```

</details>

#### rejects segments with filesz larger than memsz

1. var bytes = make rv64 exec
2. bytes[96] = 8 to u8
3. bytes[104] = 4 to u8
   - Expected: image.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = make_rv64_exec()
bytes[96] = 8.to_u8()
bytes[104] = 4.to_u8()
val image = load_riscv_executable(bytes, Architecture.Riscv64)
expect(image.is_err()).to_equal(true)
```

</details>

#### parses a minimal x86_64 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_riscv_executable(make_x86_64_exec(), Architecture.X86_64)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf64)
expect(loaded.entry).to_equal(0x400000)
expect(loaded.segments.len()).to_equal(1)
```

</details>

#### parses a minimal x86_32 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_user_executable(make_x86_32_exec(), Architecture.X86)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf32)
expect(loaded.entry).to_equal(0x8048000)
expect(loaded.segments.len()).to_equal(1)
expect(loaded.segments[0].virt_addr).to_equal(0x8048000)
```

</details>

#### parses a minimal ARM64 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_user_executable(make_arm64_exec(), Architecture.Arm64)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf64)
expect(loaded.entry).to_equal(0x400000)
expect(loaded.segments.len()).to_equal(1)
```

</details>

#### parses a minimal ARM32 executable load plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = load_user_executable(make_arm32_exec(), Architecture.Arm32)
expect(image.is_ok()).to_equal(true)
val loaded = image.unwrap()
expect(loaded.class_).to_equal(ElfClass.Elf32)
expect(loaded.entry).to_equal(0x80000000)
expect(loaded.segments.len()).to_equal(1)
```

</details>

#### rejects ARM machine mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(load_user_executable(make_arm64_exec(), Architecture.Arm32).is_err()).to_equal(true)
expect(load_user_executable(make_arm32_exec(), Architecture.Arm64).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/elf_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ELF loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
