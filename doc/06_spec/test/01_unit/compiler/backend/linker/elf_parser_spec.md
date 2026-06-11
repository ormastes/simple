# Elf Parser Specification

> <details>

<!-- sdn-diagram:id=elf_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf_parser_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Parser Specification

## Scenarios

### ELF Parser - header parsing

#### parses a minimal ELF header from bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr_bytes = make_elf_header_bytes(0, 0, 0)
val result = elf_parse_header(hdr_bytes)
expect(result.is_ok()).to_equal(true)
val hdr = result.unwrap()
expect(hdr.e_type).to_equal(1)      # ET_REL
expect(hdr.e_machine).to_equal(62)  # EM_X86_64
```

</details>

#### returns error on too-short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_bytes: [i64] = [0x7f, 0x45, 0x4c, 0x46]
val result = elf_parse_header(short_bytes)
expect(result.is_ok()).to_equal(false)
```

</details>

#### returns error on bad magic bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [i64] = [
    0x00, 0x00, 0x00, 0x00,
    2, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0x3e, 0,
    1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0,
    64, 0, 56, 0, 0, 0, 64, 0,
    0, 0, 0, 0
]
val result = elf_parse_header(bad_bytes)
expect(result.is_ok()).to_equal(false)
```

</details>

### ELF Parser - string table

#### reads a string from a string table by index

1. sh addr: 0,    # file offset = 0
   - Expected: strtab.data.len() equals `9`
   - Expected: elf_strtab_get(strtab, 0) equals ``
   - Expected: elf_strtab_get(strtab, 1) equals `foo`
   - Expected: elf_strtab_get(strtab, 5) equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# strtab bytes: NUL, 'f', 'o', 'o', NUL, 'b', 'a', 'r', NUL
val strtab_section = ElfSectionHeader(
    sh_name: 0,
    sh_type: SHT_STRTAB,
    sh_flags: 0,
    sh_addr: 0,    # file offset = 0 (data starts at byte 0 of our slice)
    sh_size: 9
)
val raw: [i64] = [0, 102, 111, 111, 0, 98, 97, 114, 0]
val strtab = elf_parse_string_table(raw, strtab_section)
expect(strtab.data.len()).to_equal(9)
expect(elf_strtab_get(strtab, 0)).to_equal("")
expect(elf_strtab_get(strtab, 1)).to_equal("foo")
expect(elf_strtab_get(strtab, 5)).to_equal("bar")
```

</details>

#### returns empty string for out-of-range index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strtab = elf_make_empty_strtab()
expect(elf_strtab_get(strtab, 0)).to_equal("")
expect(elf_strtab_get(strtab, 999)).to_equal("")
```

</details>

### ELF Parser - symbol binding and type helpers

#### extracts binding from st_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# STB_LOCAL=0, STT_FUNC=2 => st_info = (0 << 4) | 2 = 2
val sym_local_func = ElfSymbol(st_name: 0, st_info: 2, st_other: 0, st_shndx: 1, st_value: 0, st_size: 0, name: "")
expect(elf_symbol_binding(sym_local_func)).to_equal(STB_LOCAL)
expect(elf_symbol_type(sym_local_func)).to_equal(STT_FUNC)
```

</details>

#### extracts global binding from st_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# STB_GLOBAL=1, STT_OBJECT=1 => st_info = (1 << 4) | 1 = 17
val sym_global_obj = ElfSymbol(st_name: 0, st_info: 17, st_other: 0, st_shndx: 2, st_value: 0, st_size: 0, name: "")
expect(elf_symbol_binding(sym_global_obj)).to_equal(STB_GLOBAL)
expect(elf_symbol_type(sym_global_obj)).to_equal(STT_OBJECT)
```

</details>

#### extracts weak binding from st_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# STB_WEAK=2, STT_NOTYPE=0 => st_info = (2 << 4) | 0 = 32
val sym_weak = ElfSymbol(st_name: 0, st_info: 32, st_other: 0, st_shndx: 0, st_value: 0, st_size: 0, name: "")
expect(elf_symbol_binding(sym_weak)).to_equal(STB_WEAK)
expect(elf_symbol_type(sym_weak)).to_equal(STT_NOTYPE)
```

</details>

### ELF Parser - symbol table parsing

#### parses symbol table entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build: strtab = [NUL, 'm', 'a', 'i', 'n', NUL]
# Symbol 0 (null): st_name=0, st_info=0, st_other=0, st_shndx=0, st_value=0, st_size=0
# Symbol 1 (main): st_name=1, st_info=(STB_GLOBAL<<4)|STT_FUNC=18, st_other=0, st_shndx=1, st_value=0x100, st_size=32
val strtab_data: [i64] = [0, 109, 97, 105, 110, 0]  # NUL, 'm','a','i','n', NUL
val strtab = ElfStringTable(data: strtab_data, offset: 0)

val sym0 = make_sym_entry(0, 0, 0, 0, 0, 0)
val sym1 = make_sym_entry(1, 18, 0, 1, 0x100, 32)
val sym_bytes = concat_bytes(sym0, sym1)

val symtab_section = ElfSectionHeader(
    sh_name: 0,
    sh_type: SHT_SYMTAB,
    sh_flags: 0,
    sh_addr: 0,      # file offset = 0
    sh_size: 48      # 2 symbols * 24 bytes
)

val symbols = elf_parse_symbols(sym_bytes, symtab_section, strtab)
expect(symbols.len()).to_equal(2)

val s0 = symbols[0]
expect(s0.st_name).to_equal(0)
expect(s0.st_shndx).to_equal(0)
expect(s0.st_value).to_equal(0)

val s1 = symbols[1]
expect(s1.st_name).to_equal(1)
expect(s1.st_info).to_equal(18)
expect(s1.st_shndx).to_equal(1)
expect(s1.st_value).to_equal(0x100)
expect(s1.st_size).to_equal(32)
expect(s1.name).to_equal("main")
```

</details>

### ELF Parser - relocation parsing

#### parses RELA relocation entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# One RELA entry: r_offset=0x8, r_info=0x200000001 (sym=2, type=1), r_addend=-4
val r_info: i64 = (2 << 32) | 1
val r_addend: i64 = -4
val rela_bytes = make_rela_entry(0x8, r_info, r_addend)

val rela_section = ElfSectionHeader(
    sh_name: 0,
    sh_type: SHT_RELA,
    sh_flags: 0,
    sh_addr: 0,
    sh_size: 24
)

val relocs = elf_parse_relocations(rela_bytes, rela_section)
expect(relocs.len()).to_equal(1)
val r = relocs[0]
expect(r.r_offset).to_equal(8)
expect(elf_reloc_sym(r)).to_equal(2)
expect(elf_reloc_type(r)).to_equal(1)
```

</details>

#### extracts sym index and type from r_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r_info: i64 = (5 << 32) | 42
val reloc = ElfRelocation(r_offset: 0, r_info: r_info, r_addend: 0)
expect(elf_reloc_sym(reloc)).to_equal(5)
expect(elf_reloc_type(reloc)).to_equal(42)
```

</details>

### ELF Parser - defined and undefined symbols

#### separates defined from undefined symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defined_sym = ElfSymbol(st_name: 1, st_info: 18, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 16, name: "foo")
val undef_sym = ElfSymbol(st_name: 5, st_info: 16, st_other: 0, st_shndx: 0, st_value: 0, st_size: 0, name: "bar")

# Build a minimal ElfObject to test the filter functions
val empty_strtab = elf_make_empty_strtab()
val empty_sections: [ElfSectionHeader] = []
val empty_relocs: [ElfRelocation] = []
val raw: [i64] = []
val fake_header = ElfHeader(e_type: 1, e_machine: 62, e_entry: 0, e_phoff: 0, e_shoff: 0, e_shnum: 0, e_shstrndx: 0)

val obj = ElfObject(
    header: fake_header,
    sections: empty_sections,
    symbols: [defined_sym, undef_sym],
    relocations: empty_relocs,
    strtab: empty_strtab,
    shstrtab: empty_strtab,
    raw: raw
)

val defined = elf_defined_symbols(obj)
val undefined = elf_undefined_symbols(obj)

expect(defined.len()).to_equal(1)
expect(defined[0].name).to_equal("foo")
expect(undefined.len()).to_equal(1)
expect(undefined[0].name).to_equal("bar")
```

</details>

### ELF Parser - find section by type

#### finds a section by sh_type

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sec_null = ElfSectionHeader(sh_name: 0, sh_type: SHT_NULL, sh_flags: 0, sh_addr: 0, sh_size: 0)
val sec_strtab = ElfSectionHeader(sh_name: 1, sh_type: SHT_STRTAB, sh_flags: 0, sh_addr: 64, sh_size: 10)
val sec_symtab = ElfSectionHeader(sh_name: 2, sh_type: SHT_SYMTAB, sh_flags: 0, sh_addr: 128, sh_size: 24)

val empty_strtab = elf_make_empty_strtab()
val fake_header = ElfHeader(e_type: 1, e_machine: 62, e_entry: 0, e_phoff: 0, e_shoff: 0, e_shnum: 3, e_shstrndx: 1)
val obj = ElfObject(
    header: fake_header,
    sections: [sec_null, sec_strtab, sec_symtab],
    symbols: [],
    relocations: [],
    strtab: empty_strtab,
    shstrtab: empty_strtab,
    raw: []
)

val found_strtab = elf_find_section_by_type(obj, SHT_STRTAB)
expect(found_strtab != nil).to_equal(true)
if found_strtab != nil:
    expect(found_strtab.sh_type).to_equal(SHT_STRTAB)

val found_rela = elf_find_section_by_type(obj, SHT_RELA)
expect(found_rela == nil).to_equal(true)
```

</details>

### ELF Parser - full object parsing

#### parses a minimal ELF object with no sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr_bytes = make_elf_header_bytes(0, 0, 0)
val result = elf_parse_object(hdr_bytes)
expect(result.is_ok()).to_equal(true)
val obj = result.unwrap()
expect(obj.header.e_type).to_equal(1)
expect(obj.header.e_machine).to_equal(62)
expect(obj.sections.len()).to_equal(0)
expect(obj.symbols.len()).to_equal(0)
expect(obj.relocations.len()).to_equal(0)
```

</details>

#### returns error on too-short input for object parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_bytes: [i64] = [0x7f, 0x45]
val result = elf_parse_object(short_bytes)
expect(result.is_ok()).to_equal(false)
```

</details>

#### returns error on bad magic for object parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [i64] = [
    0xDE, 0xAD, 0xBE, 0xEF,
    2, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0x3e, 0,
    1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0,
    64, 0, 56, 0, 0, 0, 64, 0,
    0, 0, 0, 0
]
val result = elf_parse_object(bad_bytes)
expect(result.is_ok()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/elf_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ELF Parser - header parsing
- ELF Parser - string table
- ELF Parser - symbol binding and type helpers
- ELF Parser - symbol table parsing
- ELF Parser - relocation parsing
- ELF Parser - defined and undefined symbols
- ELF Parser - find section by type
- ELF Parser - full object parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
