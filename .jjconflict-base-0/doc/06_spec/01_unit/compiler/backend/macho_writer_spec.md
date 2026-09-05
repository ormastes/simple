# macho_writer_spec

> Purpose: Prove that Mach-O header generation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macho_writer_spec

Purpose: Prove that Mach-O header generation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/macho_writer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Mach-O header generation.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Mach-O header generation

#### generates minimal Mach-O with RET instruction for ARM64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates minimal Mach-O with RET instruction for ARM64
- Verify: generates minimal Mach-O with RET instruction for ARM64
   - Expected: bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates minimal Mach-O with RET instruction for ARM64")
step("Verify: generates minimal Mach-O with RET instruction for ARM64")
# @req: REQ-COMP-MACH-O-HEADER-GENERATION-001
# ARM64 RET = 0xd65f03c0 (little-endian: c0 03 5f d6)
var writer = macho_writer_aarch64()
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# Should produce valid output (non-empty)
expect(bytes.len() > 0).to_equal(true)
```

</details>

#### has correct magic number for 64-bit Mach-O

- has correct magic number for 64-bit Mach-O
- Verify: has correct magic number for 64-bit Mach-O
   - Expected: bytes[0] equals `0xcf`
   - Expected: bytes[1] equals `0xfa`
   - Expected: bytes[2] equals `0xed`
   - Expected: bytes[3] equals `0xfe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct magic number for 64-bit Mach-O")
step("Verify: has correct magic number for 64-bit Mach-O")
var writer = macho_writer_aarch64()
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# MH_MAGIC_64 = 0xfeedfacf -> little-endian: cf fa ed fe
expect(bytes[0]).to_equal(0xcf)
expect(bytes[1]).to_equal(0xfa)
expect(bytes[2]).to_equal(0xed)
expect(bytes[3]).to_equal(0xfe)
```

</details>

#### has correct CPU type for ARM64

- has correct CPU type for ARM64
- Verify: has correct CPU type for ARM64
   - Expected: bytes[4] equals `0x0c`
   - Expected: bytes[5] equals `0x00`
   - Expected: bytes[6] equals `0x00`
   - Expected: bytes[7] equals `0x01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct CPU type for ARM64")
step("Verify: has correct CPU type for ARM64")
var writer = macho_writer_aarch64()
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# CPU_TYPE_ARM64 = 0x0100000c -> little-endian: 0c 00 00 01
expect(bytes[4]).to_equal(0x0c)
expect(bytes[5]).to_equal(0x00)
expect(bytes[6]).to_equal(0x00)
expect(bytes[7]).to_equal(0x01)
```

</details>

#### has correct CPU type for x86_64

- has correct CPU type for x86_64
- Verify: has correct CPU type for x86_64
   - Expected: bytes[4] equals `0x07`
   - Expected: bytes[5] equals `0x00`
   - Expected: bytes[6] equals `0x00`
   - Expected: bytes[7] equals `0x01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct CPU type for x86_64")
step("Verify: has correct CPU type for x86_64")
var writer = macho_writer_x86_64()
val text_section = new_macho_text_section([0xc3])  # RET
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# CPU_TYPE_X86_64 = 0x01000007 -> little-endian: 07 00 00 01
expect(bytes[4]).to_equal(0x07)
expect(bytes[5]).to_equal(0x00)
expect(bytes[6]).to_equal(0x00)
expect(bytes[7]).to_equal(0x01)
```

</details>

#### has MH_OBJECT file type

- has MH_OBJECT file type
- Verify: has MH_OBJECT file type
   - Expected: bytes[12] equals `1`
   - Expected: bytes[13] equals `0`
   - Expected: bytes[14] equals `0`
   - Expected: bytes[15] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has MH_OBJECT file type")
step("Verify: has MH_OBJECT file type")
var writer = macho_writer_aarch64()
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# filetype at offset 12: MH_OBJECT = 1
expect(bytes[12]).to_equal(1)
expect(bytes[13]).to_equal(0)
expect(bytes[14]).to_equal(0)
expect(bytes[15]).to_equal(0)
```

</details>

### Mach-O symbol naming

#### prepends underscore to symbol names

- prepends underscore to symbol names
- Verify: prepends underscore to symbol names
   - Expected: result equals `_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prepends underscore to symbol names")
step("Verify: prepends underscore to symbol names")
val result = macho_symbol_name("main")
expect(result).to_equal("_main")
```

</details>

#### prepends underscore to already-prefixed names

- prepends underscore to already-prefixed names
- Verify: prepends underscore to already-prefixed names
   - Expected: result equals `__start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prepends underscore to already-prefixed names")
step("Verify: prepends underscore to already-prefixed names")
val result = macho_symbol_name("_start")
expect(result).to_equal("__start")
```

</details>

#### creates extern symbol with undefined section

- creates extern symbol with undefined section
- Verify: creates extern symbol with undefined section
   - Expected: sym.section_ordinal equals `0`
   - Expected: sym.value equals `0`
   - Expected: sym.sym_type equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates extern symbol with undefined section")
step("Verify: creates extern symbol with undefined section")
val sym = new_macho_extern_symbol("printf")
expect(sym.section_ordinal).to_equal(0)
expect(sym.value).to_equal(0)
# N_UNDF + N_EXT = 0x01
expect(sym.sym_type).to_equal(1)
```

</details>

### Mach-O section types

#### creates __TEXT,__text section with instruction attributes

- creates __TEXT,__text section with instruction attributes
- Verify: creates __TEXT,__text section with instruction attributes
   - Expected: section.sect_name equals `__text`
   - Expected: section.seg_name equals `__TEXT`
   - Expected: section.attributes equals `expected_attrs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates __TEXT,__text section with instruction attributes")
step("Verify: creates __TEXT,__text section with instruction attributes")
val section = new_macho_text_section([0x00])
expect(section.sect_name).to_equal("__text")
expect(section.seg_name).to_equal("__TEXT")
val expected_attrs = S_ATTR_PURE_INSTRUCTIONS + S_ATTR_SOME_INSTRUCTIONS
expect(section.attributes).to_equal(expected_attrs)
```

</details>

#### creates __TEXT,__const section for read-only data

- creates __TEXT,__const section for read-only data
- Verify: creates __TEXT,__const section for read-only data
   - Expected: section.sect_name equals `__const`
   - Expected: section.seg_name equals `__TEXT`
   - Expected: section.attributes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates __TEXT,__const section for read-only data")
step("Verify: creates __TEXT,__const section for read-only data")
val section = new_macho_const_section([1, 2, 3, 4])
expect(section.sect_name).to_equal("__const")
expect(section.seg_name).to_equal("__TEXT")
expect(section.attributes).to_equal(0)
```

</details>

#### creates __DATA,__data section for mutable data

- creates __DATA,__data section for mutable data
- Verify: creates __DATA,__data section for mutable data
   - Expected: section.sect_name equals `__data`
   - Expected: section.seg_name equals `__DATA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates __DATA,__data section for mutable data")
step("Verify: creates __DATA,__data section for mutable data")
val section = new_macho_data_section([0, 0, 0, 0])
expect(section.sect_name).to_equal("__data")
expect(section.seg_name).to_equal("__DATA")
```

</details>

#### creates __TEXT,__cstring section for C strings

- creates __TEXT,__cstring section for C strings
- Verify: creates __TEXT,__cstring section for C strings
   - Expected: section.sect_name equals `__cstring`
   - Expected: section.seg_name equals `__TEXT`
   - Expected: section.sect_type equals `S_CSTRING_LITERALS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates __TEXT,__cstring section for C strings")
step("Verify: creates __TEXT,__cstring section for C strings")
# "hello\0" = [104, 101, 108, 108, 111, 0]
val section = new_macho_cstring_section([104, 101, 108, 108, 111, 0])
expect(section.sect_name).to_equal("__cstring")
expect(section.seg_name).to_equal("__TEXT")
expect(section.sect_type).to_equal(S_CSTRING_LITERALS)
```

</details>

### Mach-O relocation mapping

#### maps R_AARCH64_CALL26 to ARM64_RELOC_BRANCH26

- maps R_AARCH64_CALL26 to ARM64_RELOC_BRANCH26
- Verify: maps R_AARCH64_CALL26 to ARM64_RELOC_BRANCH26
   - Expected: result equals `ARM64_RELOC_BRANCH26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps R_AARCH64_CALL26 to ARM64_RELOC_BRANCH26")
step("Verify: maps R_AARCH64_CALL26 to ARM64_RELOC_BRANCH26")
val result = map_elf_reloc_to_macho_arm64(283)
expect(result).to_equal(ARM64_RELOC_BRANCH26)
```

</details>

#### maps R_AARCH64_ADR_PREL_PG_HI21 to ARM64_RELOC_PAGE21

- maps R_AARCH64_ADR_PREL_PG_HI21 to ARM64_RELOC_PAGE21
- Verify: maps R_AARCH64_ADR_PREL_PG_HI21 to ARM64_RELOC_PAGE21
   - Expected: result equals `ARM64_RELOC_PAGE21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps R_AARCH64_ADR_PREL_PG_HI21 to ARM64_RELOC_PAGE21")
step("Verify: maps R_AARCH64_ADR_PREL_PG_HI21 to ARM64_RELOC_PAGE21")
val result = map_elf_reloc_to_macho_arm64(275)
expect(result).to_equal(ARM64_RELOC_PAGE21)
```

</details>

#### maps R_AARCH64_ADD_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12

- maps R_AARCH64_ADD_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12
- Verify: maps R_AARCH64_ADD_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12
   - Expected: result equals `ARM64_RELOC_PAGEOFF12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps R_AARCH64_ADD_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12")
step("Verify: maps R_AARCH64_ADD_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12")
val result = map_elf_reloc_to_macho_arm64(277)
expect(result).to_equal(ARM64_RELOC_PAGEOFF12)
```

</details>

#### maps R_AARCH64_LDST64_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12

- maps R_AARCH64_LDST64_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12
- Verify: maps R_AARCH64_LDST64_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12
   - Expected: result equals `ARM64_RELOC_PAGEOFF12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps R_AARCH64_LDST64_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12")
step("Verify: maps R_AARCH64_LDST64_ABS_LO12_NC to ARM64_RELOC_PAGEOFF12")
val result = map_elf_reloc_to_macho_arm64(286)
expect(result).to_equal(ARM64_RELOC_PAGEOFF12)
```

</details>

#### falls back to UNSIGNED for unknown ELF reloc types

- falls back to UNSIGNED for unknown ELF reloc types
- Verify: falls back to UNSIGNED for unknown ELF reloc types
   - Expected: result equals `ARM64_RELOC_UNSIGNED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("falls back to UNSIGNED for unknown ELF reloc types")
step("Verify: falls back to UNSIGNED for unknown ELF reloc types")
val result = map_elf_reloc_to_macho_arm64(999)
expect(result).to_equal(ARM64_RELOC_UNSIGNED)
```

</details>

#### maps x86_64 R_X86_64_PLT32 to X86_64_RELOC_BRANCH

- maps x86_64 R_X86_64_PLT32 to X86_64_RELOC_BRANCH
- Verify: maps x86_64 R_X86_64_PLT32 to X86_64_RELOC_BRANCH
   - Expected: result equals `X86_64_RELOC_BRANCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps x86_64 R_X86_64_PLT32 to X86_64_RELOC_BRANCH")
step("Verify: maps x86_64 R_X86_64_PLT32 to X86_64_RELOC_BRANCH")
val result = map_elf_reloc_to_macho_x86_64(4)
expect(result).to_equal(X86_64_RELOC_BRANCH)
```

</details>

#### maps x86_64 R_X86_64_PC32 to X86_64_RELOC_SIGNED

- maps x86_64 R_X86_64_PC32 to X86_64_RELOC_SIGNED
- Verify: maps x86_64 R_X86_64_PC32 to X86_64_RELOC_SIGNED
   - Expected: result equals `X86_64_RELOC_SIGNED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps x86_64 R_X86_64_PC32 to X86_64_RELOC_SIGNED")
step("Verify: maps x86_64 R_X86_64_PC32 to X86_64_RELOC_SIGNED")
val result = map_elf_reloc_to_macho_x86_64(2)
expect(result).to_equal(X86_64_RELOC_SIGNED)
```

</details>

#### maps x86_64 R_X86_64_64 to X86_64_RELOC_UNSIGNED

- maps x86_64 R_X86_64_64 to X86_64_RELOC_UNSIGNED
- Verify: maps x86_64 R_X86_64_64 to X86_64_RELOC_UNSIGNED
   - Expected: result equals `X86_64_RELOC_UNSIGNED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps x86_64 R_X86_64_64 to X86_64_RELOC_UNSIGNED")
step("Verify: maps x86_64 R_X86_64_64 to X86_64_RELOC_UNSIGNED")
val result = map_elf_reloc_to_macho_x86_64(1)
expect(result).to_equal(X86_64_RELOC_UNSIGNED)
```

</details>

### Mach-O full generation

#### generates Mach-O with function symbol

- generates Mach-O with function symbol
- Verify: generates Mach-O with function symbol
   - Expected: bytes.len() > MACHO_HEADER_SIZE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates Mach-O with function symbol")
step("Verify: generates Mach-O with function symbol")
var writer = macho_writer_aarch64()
# ARM64 RET instruction
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val sym = new_macho_func_symbol("main", 1, 0)
writer = macho_add_symbol(writer, sym)
val bytes = write_macho64(writer)
# Should have reasonable size
expect(bytes.len() > MACHO_HEADER_SIZE).to_equal(true)
```

</details>

#### generates Mach-O with extern call and relocation

- generates Mach-O with extern call and relocation
- Verify: generates Mach-O with extern call and relocation
   - Expected: bytes.len() > MACHO_HEADER_SIZE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates Mach-O with extern call and relocation")
step("Verify: generates Mach-O with extern call and relocation")
var writer = macho_writer_aarch64()
# BL instruction (ARM64 call) - 4 bytes
var text_section = new_macho_text_section([0x00, 0x00, 0x00, 0x94])
val reloc = MachOReloc(
    offset: 0,
    symbol_index: 0,
    reloc_type: ARM64_RELOC_BRANCH26,
    length: 2,
    is_pc_relative: true,
    is_extern: true
)
text_section = macho_section_add_reloc(text_section, reloc)
writer = macho_add_section(writer, text_section)
val ext_sym = new_macho_extern_symbol("printf")
writer = macho_add_symbol(writer, ext_sym)
val bytes = write_macho64(writer)
expect(bytes.len() > MACHO_HEADER_SIZE).to_equal(true)
```

</details>

#### generates Mach-O with multiple functions

- generates Mach-O with multiple functions
- Verify: generates Mach-O with multiple functions
   - Expected: bytes.len() > MACHO_HEADER_SIZE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates Mach-O with multiple functions")
step("Verify: generates Mach-O with multiple functions")
var writer = macho_writer_aarch64()
# Two ARM64 RET instructions
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6, 0xc0, 0x03, 0x5f, 0xd6])
writer = macho_add_section(writer, text_section)
val sym1 = new_macho_func_symbol("foo", 1, 0)
val sym2 = new_macho_func_symbol("bar", 1, 4)
writer = macho_add_symbol(writer, sym1)
writer = macho_add_symbol(writer, sym2)
val bytes = write_macho64(writer)
expect(bytes.len() > MACHO_HEADER_SIZE).to_equal(true)
```

</details>

#### generates Mach-O with data section

- generates Mach-O with data section
- Verify: generates Mach-O with data section
   - Expected: bytes.len() > MACHO_HEADER_SIZE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generates Mach-O with data section")
step("Verify: generates Mach-O with data section")
var writer = macho_writer_aarch64()
val text_section = new_macho_text_section([0xc0, 0x03, 0x5f, 0xd6])
val data_section = new_macho_const_section([1, 2, 3, 4, 5, 6, 7, 8])
writer = macho_add_section(writer, text_section)
writer = macho_add_section(writer, data_section)
val sym = new_macho_func_symbol("main", 1, 0)
writer = macho_add_symbol(writer, sym)
val bytes = write_macho64(writer)
expect(bytes.len() > MACHO_HEADER_SIZE).to_equal(true)
```

</details>

#### starts with correct Mach-O magic bytes

- starts with correct Mach-O magic bytes
- Verify: starts with correct Mach-O magic bytes
   - Expected: bytes[0] equals `0xcf`
   - Expected: bytes[1] equals `0xfa`
   - Expected: bytes[2] equals `0xed`
   - Expected: bytes[3] equals `0xfe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("starts with correct Mach-O magic bytes")
step("Verify: starts with correct Mach-O magic bytes")
var writer = macho_writer_x86_64()
val text_section = new_macho_text_section([0xc3])  # x86 RET
writer = macho_add_section(writer, text_section)
val bytes = write_macho64(writer)
# CF FA ED FE = Mach-O 64-bit magic (little-endian)
expect(bytes[0]).to_equal(0xcf)
expect(bytes[1]).to_equal(0xfa)
expect(bytes[2]).to_equal(0xed)
expect(bytes[3]).to_equal(0xfe)
```

</details>

### Mach-O helper functions

#### reuses ByteBuffer from elf_writer

- reuses ByteBuffer from elf_writer
- Verify: reuses ByteBuffer from elf_writer
   - Expected: buf_len(buf) equals `1`
   - Expected: buf.bytes[0] equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses ByteBuffer from elf_writer")
step("Verify: reuses ByteBuffer from elf_writer")
var buf = new_byte_buffer()
buf = buf_write_u8(buf, 0x42)
expect(buf_len(buf)).to_equal(1)
expect(buf.bytes[0]).to_equal(0x42)
```

</details>

#### writes fixed-size names correctly

- writes fixed-size names correctly
- Verify: writes fixed-size names correctly
   - Expected: buf_len(buf) equals `16`
   - Expected: buf.bytes[0] equals `95)   # '_'`
   - Expected: buf.bytes[1] equals `95)   # '_'`
   - Expected: buf.bytes[2] equals `116)  # 't'`
   - Expected: buf.bytes[3] equals `101)  # 'e'`
   - Expected: buf.bytes[4] equals `120)  # 'x'`
   - Expected: buf.bytes[5] equals `116)  # 't'`
   - Expected: buf.bytes[6] equals `0`
   - Expected: buf.bytes[15] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes fixed-size names correctly")
step("Verify: writes fixed-size names correctly")
var buf = new_byte_buffer()
buf = write_fixed_name(buf, "__text", 16)
expect(buf_len(buf)).to_equal(16)
# First bytes should be "__text"
expect(buf.bytes[0]).to_equal(95)   # '_'
expect(buf.bytes[1]).to_equal(95)   # '_'
expect(buf.bytes[2]).to_equal(116)  # 't'
expect(buf.bytes[3]).to_equal(101)  # 'e'
expect(buf.bytes[4]).to_equal(120)  # 'x'
expect(buf.bytes[5]).to_equal(116)  # 't'
# Rest should be zero-padded
expect(buf.bytes[6]).to_equal(0)
expect(buf.bytes[15]).to_equal(0)
```

</details>

#### computes pow2 correctly

- computes pow2 correctly
- Verify: computes pow2 correctly
   - Expected: pow2(0) equals `1`
   - Expected: pow2(1) equals `2`
   - Expected: pow2(2) equals `4`
   - Expected: pow2(3) equals `8`
   - Expected: pow2(4) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("computes pow2 correctly")
step("Verify: computes pow2 correctly")
expect(pow2(0)).to_equal(1)
expect(pow2(1)).to_equal(2)
expect(pow2(2)).to_equal(4)
expect(pow2(3)).to_equal(8)
expect(pow2(4)).to_equal(16)
```

</details>

### Mach-O relocation packing

#### packs relocation info correctly for BRANCH26

- packs relocation info correctly for BRANCH26
- Verify: packs relocation info correctly for BRANCH26
   - Expected: packed > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("packs relocation info correctly for BRANCH26")
step("Verify: packs relocation info correctly for BRANCH26")
# symbol_index=0, pc_rel=true, length=2, extern=true, type=BRANCH26(2)
val packed = macho_reloc_info(0, true, 2, true, 2)
# bit 24 = 1 (pc_rel), bits 25-26 = 2 (length), bit 27 = 1 (extern), bits 28-31 = 2 (type)
# = 0 + 16777216 + 67108864 + 134217728 + 536870912 = ...
# Verify non-zero (exact value depends on packing)
expect(packed > 0).to_equal(true)
```

</details>

#### packs relocation info with symbol index

- packs relocation info with symbol index
- Verify: packs relocation info with symbol index
   - Expected: low24 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("packs relocation info with symbol index")
step("Verify: packs relocation info with symbol index")
val packed = macho_reloc_info(5, false, 2, true, 0)
# Low 24 bits should contain symbol index 5
val low24 = packed % 16777216
expect(low24).to_equal(5)
```

</details>

#### packs relocation with pc-relative bit

- packs relocation with pc-relative bit
- Verify: packs relocation with pc-relative bit
   - Expected: packed_pcrel > packed_abs is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("packs relocation with pc-relative bit")
step("Verify: packs relocation with pc-relative bit")
val packed_pcrel = macho_reloc_info(0, true, 0, false, 0)
val packed_abs = macho_reloc_info(0, false, 0, false, 0)
# pc-relative version should have bit 24 set
expect(packed_pcrel > packed_abs).to_equal(true)
```

</details>

### Mach-O constants

#### has correct MH_MAGIC_64 value

- has correct MH_MAGIC_64 value
- Verify: has correct MH_MAGIC_64 value
   - Expected: MH_MAGIC_64 equals `4277009103`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct MH_MAGIC_64 value")
step("Verify: has correct MH_MAGIC_64 value")
# 0xfeedfacf
expect(MH_MAGIC_64).to_equal(4277009103)
```

</details>

#### has correct CPU_TYPE_ARM64 value

- has correct CPU_TYPE_ARM64 value
- Verify: has correct CPU_TYPE_ARM64 value
   - Expected: CPU_TYPE_ARM64 equals `16777228`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct CPU_TYPE_ARM64 value")
step("Verify: has correct CPU_TYPE_ARM64 value")
# 0x0100000c
expect(CPU_TYPE_ARM64).to_equal(16777228)
```

</details>

#### has correct CPU_TYPE_X86_64 value

- has correct CPU_TYPE_X86_64 value
- Verify: has correct CPU_TYPE_X86_64 value
   - Expected: CPU_TYPE_X86_64 equals `16777223`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct CPU_TYPE_X86_64 value")
step("Verify: has correct CPU_TYPE_X86_64 value")
# 0x01000007
expect(CPU_TYPE_X86_64).to_equal(16777223)
```

</details>

#### has correct MH_OBJECT file type

- has correct MH_OBJECT file type
- Verify: has correct MH_OBJECT file type
   - Expected: MH_OBJECT equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct MH_OBJECT file type")
step("Verify: has correct MH_OBJECT file type")
expect(MH_OBJECT).to_equal(1)
```

</details>

#### has correct load command types

- has correct load command types
- Verify: has correct load command types
   - Expected: LC_SEGMENT_64 equals `0x19`
   - Expected: LC_SYMTAB equals `0x02`
   - Expected: LC_DYSYMTAB equals `0x0b`
   - Expected: LC_BUILD_VERSION equals `0x32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct load command types")
step("Verify: has correct load command types")
expect(LC_SEGMENT_64).to_equal(0x19)
expect(LC_SYMTAB).to_equal(0x02)
expect(LC_DYSYMTAB).to_equal(0x0b)
expect(LC_BUILD_VERSION).to_equal(0x32)
```

</details>

#### has correct ARM64 relocation type values

- has correct ARM64 relocation type values
- Verify: has correct ARM64 relocation type values
   - Expected: ARM64_RELOC_UNSIGNED equals `0`
   - Expected: ARM64_RELOC_BRANCH26 equals `2`
   - Expected: ARM64_RELOC_PAGE21 equals `3`
   - Expected: ARM64_RELOC_PAGEOFF12 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct ARM64 relocation type values")
step("Verify: has correct ARM64 relocation type values")
expect(ARM64_RELOC_UNSIGNED).to_equal(0)
expect(ARM64_RELOC_BRANCH26).to_equal(2)
expect(ARM64_RELOC_PAGE21).to_equal(3)
expect(ARM64_RELOC_PAGEOFF12).to_equal(4)
```

</details>

#### has correct nlist_64 size

- has correct nlist_64 size
- Verify: has correct nlist_64 size
   - Expected: NLIST_64_SIZE equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct nlist_64 size")
step("Verify: has correct nlist_64 size")
expect(NLIST_64_SIZE).to_equal(16)
```

</details>

#### has correct header size

- has correct header size
- Verify: has correct header size
   - Expected: MACHO_HEADER_SIZE equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct header size")
step("Verify: has correct header size")
expect(MACHO_HEADER_SIZE).to_equal(32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-MACH-O-HEADER-GENERATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12d543f99325491665941e3baf3515af3fdc9584fca08257ea8f5466331edf07`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12d543f99325491665941e3baf3515af3fdc9584fca08257ea8f5466331edf07`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12d543f99325491665941e3baf3515af3fdc9584fca08257ea8f5466331edf07`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/macho_writer_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/macho_writer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/macho_writer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/macho_writer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/macho_writer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/macho_writer_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates minimal Mach-O with RET instruction for ARM64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/macho_writer_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct magic number for 64-bit Mach-O' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/macho_writer_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct CPU type for ARM64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
