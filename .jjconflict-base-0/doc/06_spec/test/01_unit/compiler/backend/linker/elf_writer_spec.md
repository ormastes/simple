# Elf Writer Specification

> <details>

<!-- sdn-diagram:id=elf_writer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf_writer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf_writer_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf_writer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Writer Specification

## Scenarios

### elf_writer - config constructors

#### x86_64 config has e_machine 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
expect(cfg.e_machine).to_equal(62)
```

</details>

#### aarch64 config has e_machine 183

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_aarch64()
expect(cfg.e_machine).to_equal(183)
```

</details>

#### riscv64 config has e_machine 243

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_riscv64()
expect(cfg.e_machine).to_equal(243)
```

</details>

### elf_writer - empty object

#### produces at least ELF64_HEADER_SIZE bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val sections: [ElfWriterSection] = []
val symbols: [ElfWriterSymbol] = []
val relocs: [ElfWriterReloc] = []
val bytes = elf_write_object(cfg, sections, symbols, relocs)
expect(bytes.len() >= ELF64_HEADER_SIZE).to_equal(true)
```

</details>

#### starts with ELF magic bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
expect(bytes[0]).to_equal(0x7f)
expect(bytes[1]).to_equal(0x45)
expect(bytes[2]).to_equal(0x4c)
expect(bytes[3]).to_equal(0x46)
```

</details>

#### has e_type ET_REL at offset 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
val e_type = read_u16_le(bytes, 16)
expect(e_type).to_equal(ET_REL)
```

</details>

#### has e_machine EM_X86_64 at offset 18

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
val e_machine = read_u16_le(bytes, 18)
expect(e_machine).to_equal(EM_X86_64)
```

</details>

#### round-trips through elf_parse_object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
val result = elf_parse_object(bytes)
expect(result.is_ok()).to_equal(true)
```

</details>

### elf_writer - single .text section

#### round-trips with a .text section

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xcc, 0x90, 0xc3, 0x00],
    sh_link: 0,
    sh_info: 0
)
val bytes = elf_write_object(cfg, [text_sec], [], [])
val result = elf_parse_object(bytes)
expect(result.is_ok()).to_equal(true)
val obj = result.unwrap()
# Expect at least 5 sections: null + .text + .shstrtab + .strtab + .symtab
expect(obj.sections.len() >= 4).to_equal(true)
```

</details>

#### contains a SHT_PROGBITS section

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xcc, 0x90, 0xc3, 0x00],
    sh_link: 0,
    sh_info: 0
)
val bytes = elf_write_object(cfg, [text_sec], [], [])
val result = elf_parse_object(bytes)
val obj = result.unwrap()
expect(has_section_type(obj, SHT_PROGBITS)).to_equal(true)
```

</details>

### elf_writer - symbols with locals before globals

#### emits at least 3 symbols (null + local + global)

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xcc],
    sh_link: 0,
    sh_info: 0
)
val local_sym = ElfWriterSymbol(
    name: "local_var",
    st_info: 0x00,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val global_sym = ElfWriterSymbol(
    name: "global_func",
    st_info: 0x10,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val bytes = elf_write_object(cfg, [text_sec], [local_sym, global_sym], [])
val result = elf_parse_object(bytes)
expect(result.is_ok()).to_equal(true)
val obj = result.unwrap()
expect(obj.symbols.len() >= 3).to_equal(true)
```

</details>

#### places local binding before global binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xcc],
    sh_link: 0,
    sh_info: 0
)
# Provide global first, local second -- writer should reorder
val global_sym = ElfWriterSymbol(
    name: "global_func",
    st_info: 0x10,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val local_sym = ElfWriterSymbol(
    name: "local_var",
    st_info: 0x00,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val bytes = elf_write_object(cfg, [text_sec], [global_sym, local_sym], [])
val result = elf_parse_object(bytes)
val obj = result.unwrap()
# Symbol 0 is null; symbol 1 should be the local (binding == 0)
val first_sym = obj.symbols[1]
expect(elf_symbol_binding(first_sym)).to_equal(STB_LOCAL)
```

</details>

### elf_writer - round-trip with relocations

#### produces at least one relocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xe8, 0x00, 0x00, 0x00, 0x00],
    sh_link: 0,
    sh_info: 0
)
val sym = ElfWriterSymbol(
    name: "my_func",
    st_info: 0x12,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
# R_X86_64_PC32 = 2, sym_idx = 0 => r_info = (0 << 32) | 2 = 2
val reloc = ElfWriterReloc(
    r_offset: 1,
    r_info: 2,
    r_addend: -4,
    section_name: ".text"
)
val bytes = elf_write_object(cfg, [text_sec], [sym], [reloc])
val result = elf_parse_object(bytes)
expect(result.is_ok()).to_equal(true)
val obj = result.unwrap()
expect(obj.relocations.len() >= 1).to_equal(true)
```

</details>

#### preserves relocation r_offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xe8, 0x00, 0x00, 0x00, 0x00],
    sh_link: 0,
    sh_info: 0
)
val sym = ElfWriterSymbol(
    name: "my_func",
    st_info: 0x12,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val reloc = ElfWriterReloc(
    r_offset: 1,
    r_info: 2,
    r_addend: -4,
    section_name: ".text"
)
val bytes = elf_write_object(cfg, [text_sec], [sym], [reloc])
val obj = elf_parse_object(bytes).unwrap()
val first_reloc = obj.relocations[0]
expect(first_reloc.r_offset).to_equal(1)
```

</details>

#### preserves relocation type through round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val text_sec = ElfWriterSection(
    name: ".text",
    sh_type: 1,
    sh_flags: 6,
    data: [0xe8, 0x00, 0x00, 0x00, 0x00],
    sh_link: 0,
    sh_info: 0
)
val sym = ElfWriterSymbol(
    name: "my_func",
    st_info: 0x12,
    st_other: 0,
    st_shndx: 1,
    st_value: 0,
    st_size: 0
)
val reloc = ElfWriterReloc(
    r_offset: 0,
    r_info: 2,
    r_addend: -4,
    section_name: ".text"
)
val bytes = elf_write_object(cfg, [text_sec], [sym], [reloc])
val obj = elf_parse_object(bytes).unwrap()
val first_reloc = obj.relocations[0]
# reloc type should be R_X86_64_PC32 = 2
expect(elf_reloc_type(first_reloc)).to_equal(2)
```

</details>

### elf_writer - machine type in header

#### aarch64 config writes e_machine 183

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_aarch64()
val bytes = elf_write_object(cfg, [], [], [])
val e_machine = read_u16_le(bytes, 18)
expect(e_machine).to_equal(183)
```

</details>

#### x86_64 header has correct e_ehsize at offset 52

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
val e_ehsize = read_u16_le(bytes, 52)
expect(e_ehsize).to_equal(ELF64_HEADER_SIZE)
```

</details>

#### section header entry size at offset 58 equals ELF64_SHDR_SIZE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = elf_writer_config_x86_64()
val bytes = elf_write_object(cfg, [], [], [])
val e_shentsize = read_u16_le(bytes, 58)
expect(e_shentsize).to_equal(ELF64_SHDR_SIZE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/elf_writer_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- elf_writer - config constructors
- elf_writer - empty object
- elf_writer - single .text section
- elf_writer - symbols with locals before globals
- elf_writer - round-trip with relocations
- elf_writer - machine type in header

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
