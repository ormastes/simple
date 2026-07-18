# Linker Script Specification

> <details>

<!-- sdn-diagram:id=linker_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_script_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Script Specification

## Scenarios

### linker_script - number parser

#### parses decimal number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("1234")).to_equal(1234)
```

</details>

#### parses hex with 0x prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("0x1000")).to_equal(4096)
```

</details>

#### parses hex uppercase digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("0xAB")).to_equal(171)
```

</details>

#### parses K suffix as 1024 multiplier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("256K")).to_equal(262144)
```

</details>

#### parses M suffix as 1048576 multiplier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("1M")).to_equal(1048576)
```

</details>

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("")).to_equal(0)
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ld_parse_number("0")).to_equal(0)
```

</details>

### linker_script - tokenizer

#### tokenizes ENTRY(_start) into 5 tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens.len()).to_equal(5)
```

</details>

#### first token is Word ENTRY

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens[0].kind == LdTokenKind.Word).to_equal(true)
expect(tokens[0].value).to_equal("ENTRY")
```

</details>

#### produces correct token sequence for ENTRY(_start)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens[1].kind == LdTokenKind.LParen).to_equal(true)
expect(tokens[2].kind == LdTokenKind.Word).to_equal(true)
expect(tokens[2].value).to_equal("_start")
expect(tokens[3].kind == LdTokenKind.RParen).to_equal(true)
expect(tokens[4].kind == LdTokenKind.Eof).to_equal(true)
```

</details>

#### tokenizes empty string to single Eof

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("")
expect(tokens.len()).to_equal(1)
expect(tokens[0].kind == LdTokenKind.Eof).to_equal(true)
```

</details>

#### skips block comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("/* comment */ ENTRY(x)")
# Should have Word(ENTRY), LParen, Word(x), RParen, Eof
expect(tokens[0].value).to_equal("ENTRY")
expect(tokens[2].value).to_equal("x")
```

</details>

#### tokenizes hex number as Number kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = ld_tokenize("0x1000")
expect(tokens[0].kind == LdTokenKind.Number).to_equal(true)
expect(tokens[0].value).to_equal("0x1000")
```

</details>

### linker_script - ENTRY directive

#### parses ENTRY(_start)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = ld_parse("ENTRY(_start)").unwrap()
expect(script.entry).to_equal("_start")
```

</details>

#### parses ENTRY(main)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = ld_parse("ENTRY(main)").unwrap()
expect(script.entry).to_equal("main")
```

</details>

#### ld_has_entry returns true for parsed script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = ld_parse("ENTRY(_start)").unwrap()
expect(ld_has_entry(script)).to_equal(true)
```

</details>

### linker_script - MEMORY block

#### parses two memory regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(ld_region_count(script)).to_equal(2)
```

</details>

#### first region is FLASH with rx attrs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(script.memory[0].name).to_equal("FLASH")
expect(script.memory[0].attrs).to_equal("rx")
expect(script.memory[0].origin).to_equal(134217728)
expect(script.memory[0].length).to_equal(262144)
```

</details>

#### second region is RAM with rwx attrs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(script.memory[1].name).to_equal("RAM")
expect(script.memory[1].attrs).to_equal("rwx")
```

</details>

#### ld_find_region finds existing region

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K }"
val script = ld_parse(input).unwrap()
val region = ld_find_region(script, "FLASH")
expect(region != nil).to_equal(true)
```

</details>

#### ld_find_region returns nil for nonexistent region

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K }"
val script = ld_parse(input).unwrap()
val region = ld_find_region(script, "NONEXIST")
# `to_be_nil()` is false for an Optional-None return while the `== nil`
# operator is true; assert via the operator (hoisted so the matcher sees a bool).
val region_is_nil = region == nil
expect(region_is_nil).to_equal(true)
```

</details>

### linker_script - SECTIONS block

#### parses three output sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH .data : { *(.data) } > RAM .bss : { *(.bss) } > RAM }"
val script = ld_parse(input).unwrap()
expect(ld_section_count(script)).to_equal(3)
```

</details>

#### first section is .text with FLASH region

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH .data : { *(.data) } > RAM }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].name).to_equal(".text")
expect(script.sections[0].region).to_equal("FLASH")
```

</details>

#### first section has two input patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].inputs.len()).to_equal(2)
expect(script.sections[0].inputs[0].pattern).to_equal(".text")
```

</details>

#### ld_find_section finds existing section

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
val section = ld_find_section(script, ".text")
expect(section != nil).to_equal(true)
```

</details>

#### ld_find_section returns nil for nonexistent section

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
val section = ld_find_section(script, ".nonexist")
# `to_be_nil()` is false for an Optional-None return while the `== nil`
# operator is true; assert via the operator (hoisted so the matcher sees a bool).
val section_is_nil = section == nil
expect(section_is_nil).to_equal(true)
```

</details>

### linker_script - complete script

#### parses full script with ENTRY, MEMORY, and SECTIONS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "ENTRY(_start) MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K } SECTIONS { .text : { *(.text) } > FLASH .data : { *(.data) } > RAM }"
val script = ld_parse(input).unwrap()
expect(script.entry).to_equal("_start")
expect(ld_region_count(script)).to_equal(2)
expect(ld_section_count(script)).to_equal(2)
expect(ld_has_entry(script)).to_equal(true)
```

</details>

### linker_script - convenience functions

#### ld_script_new creates empty script

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = ld_script_new()
expect(script.entry).to_equal("")
expect(ld_section_count(script)).to_equal(0)
expect(ld_region_count(script)).to_equal(0)
```

</details>

#### ld_has_entry returns false for empty script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = ld_script_new()
expect(ld_has_entry(script)).to_equal(false)
```

</details>

### linker_script - section with explicit address

#### parses section with explicit address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .isr_vector 0x08000000 : { *(.isr_vector) } }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].address).to_equal(134217728)
```

</details>

#### section without address has address -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].address).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/linker_script_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- linker_script - number parser
- linker_script - tokenizer
- linker_script - ENTRY directive
- linker_script - MEMORY block
- linker_script - SECTIONS block
- linker_script - complete script
- linker_script - convenience functions
- linker_script - section with explicit address

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
