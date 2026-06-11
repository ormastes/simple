# Mold Pure Specification

> <details>

<!-- sdn-diagram:id=mold_pure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mold_pure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mold_pure_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mold_pure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mold Pure Specification

## Scenarios

### ELF Inspector

### elf_parse_header — bad magic

#### returns error for wrong magic byte 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [i64] = [
    0x00, 0x45, 0x4c, 0x46, 2, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
]
val result = elf_parse_header(bad)
expect(result.is_ok()).to_equal(false)
```

</details>

#### returns error for buffer smaller than 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tiny: [i64] = [0x7f, 0x45, 0x4c, 0x46]
val result = elf_parse_header(tiny)
expect(result.is_ok()).to_equal(false)
```

</details>

### elf_parse_header — valid ELF64

#### parses e_type correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_elf64_header(1, 62, 0, 0)  # ET_REL, EM_X86_64
val result = elf_parse_header(bytes)
expect(result.is_ok()).to_equal(true)
val header = result.unwrap()
expect(header.e_type).to_equal(1)
```

</details>

#### parses e_machine correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_elf64_header(1, 62, 0, 0)
val header = elf_parse_header(bytes).unwrap()
expect(header.e_machine).to_equal(62)
```

</details>

#### parses e_shnum = 0 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_elf64_header(1, 62, 0, 0)
val header = elf_parse_header(bytes).unwrap()
expect(header.e_shnum).to_equal(0)
```

</details>

### elf_inspect — section count

#### returns zero sections when e_shnum is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_elf64_header(1, 62, 0, 0)
val result = elf_inspect(bytes)
expect(result.is_ok()).to_equal(true)
val inspector = result.unwrap()
expect(inspector.sections.len()).to_equal(0)
```

</details>

### elf_has_symbol_table

#### returns true when a section has sh_type == SHT_SYMTAB

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = ElfHeader(
    e_type: 1, e_machine: 62, e_entry: 0,
    e_phoff: 0, e_shoff: 0, e_shnum: 1, e_shstrndx: 0
)
val symtab_sec = ElfSectionHeader(
    sh_name: 0, sh_type: 2, sh_flags: 0, sh_addr: 0, sh_size: 0
)
val inspector = ElfInspector(header: hdr, sections: [symtab_sec], is_valid: true)
expect(elf_has_symbol_table(inspector)).to_equal(true)
```

</details>

#### returns false when no section has sh_type == SHT_SYMTAB

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = ElfHeader(
    e_type: 1, e_machine: 62, e_entry: 0,
    e_phoff: 0, e_shoff: 0, e_shnum: 1, e_shstrndx: 0
)
val progbits_sec = ElfSectionHeader(
    sh_name: 0, sh_type: 1, sh_flags: 0, sh_addr: 0, sh_size: 0
)
val inspector = ElfInspector(header: hdr, sections: [progbits_sec], is_valid: true)
expect(elf_has_symbol_table(inspector)).to_equal(false)
```

</details>

#### returns false for empty sections list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = ElfHeader(
    e_type: 1, e_machine: 62, e_entry: 0,
    e_phoff: 0, e_shoff: 0, e_shnum: 0, e_shstrndx: 0
)
val inspector = ElfInspector(header: hdr, sections: [], is_valid: true)
expect(elf_has_symbol_table(inspector)).to_equal(false)
```

</details>

### elf_machine_name

#### returns x86_64 for machine code 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(elf_machine_name(62)).to_equal("x86_64")
```

</details>

#### returns aarch64 for machine code 183

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(elf_machine_name(183)).to_equal("aarch64")
```

</details>

#### returns riscv for machine code 243

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(elf_machine_name(243)).to_equal("riscv")
```

</details>

#### returns unknown(...) for unrecognised code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = elf_machine_name(9999)
expect(name.starts_with("unknown")).to_equal(true)
```

</details>

### Linker Error Types

### LinkerError.to_string

#### NotFound contains 'not found'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = LinkerError.NotFound("mold")
val s = err.to_string()
expect(s.contains("not found")).to_equal(true)
```

</details>

#### ExitFailure contains exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = LinkerError.ExitFailure(1, "link failed")
val s = err.to_string()
expect(s.contains("1")).to_equal(true)
```

</details>

#### Timeout produces non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = LinkerError.Timeout
val s = err.to_string()
expect(s.len()).to_be_greater_than(0)
```

</details>

#### UnsupportedTarget contains target name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = LinkerError.UnsupportedTarget("riscv32-none")
val s = err.to_string()
expect(s.contains("riscv32-none")).to_equal(true)
```

</details>

### parse_linker_diagnostics

#### parses an error line with file and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = parse_linker_diagnostics("foo.o: error: undefined symbol bar")
expect(diags.len()).to_be_greater_than(0)
val d = diags[0]
expect(d.level).to_equal("error")
```

</details>

#### returns empty list for empty stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = parse_linker_diagnostics("")
expect(diags.len()).to_equal(0)
```

</details>

#### parses a warning line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = parse_linker_diagnostics("baz.o: warning: unused symbol qux")
expect(diags.len()).to_be_greater_than(0)
val d = diags[0]
expect(d.level).to_equal("warning")
```

</details>

#### handles multiple lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "a.o: error: undefined symbol foo\nb.o: warning: deprecated"
val diags = parse_linker_diagnostics(stderr)
expect(diags.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/mold_pure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ELF Inspector
- elf_parse_header — bad magic
- elf_parse_header — valid ELF64
- elf_inspect — section count
- elf_has_symbol_table
- elf_machine_name
- Linker Error Types
- LinkerError.to_string
- parse_linker_diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
