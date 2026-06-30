# Elf Load Chain Specification

> <details>

<!-- sdn-diagram:id=elf_load_chain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf_load_chain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf_load_chain_spec -> std
elf_load_chain_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf_load_chain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Load Chain Specification

## Scenarios

### ELF Loader — magic validation

#### rejects empty bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = []
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects too-short bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0x7F, 0x45, 0x4C]
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects invalid magic

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _make_bytes(64, 0)
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

### ELF Loader — valid ELF64 x86_64 header

#### parses minimal valid ELF64 x86_64 header

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _make_minimal_elf64_x86()
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

### ELF Loader — valid ELF64 RISC-V header

#### parses minimal valid ELF64 RV64 header

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _make_minimal_elf64_rv64()
val result = load_user_executable(bytes, Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

### ElfImage — struct accessors

#### ElfLoadSegment stores fields correctly

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = ElfLoadSegment(
    file_offset: 0x1000,
    file_size:   0x200,
    virt_addr:   0x400000,
    mem_size:    0x300,
    flags:       5,
    align:       0x1000
)
expect(seg.file_offset as i64).to_equal(0x1000)
expect(seg.virt_addr as i64).to_equal(0x400000)
expect(seg.mem_size > seg.file_size).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/elf_load_chain_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ELF Loader — magic validation
- ELF Loader — valid ELF64 x86_64 header
- ELF Loader — valid ELF64 RISC-V header
- ElfImage — struct accessors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
