# linker_script_spec

> Purpose: Prove that linker_script - number parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# linker_script_spec

Purpose: Prove that linker_script - number parser.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/linker/linker_script_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that linker_script - number parser.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### linker_script - number parser

#### parses decimal number

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses decimal number
- Verify: parses decimal number
   - Expected: ld_parse_number("1234") equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses decimal number")
step("Verify: parses decimal number")
# @req: REQ-COMPILER-BACKEND-001
expect(ld_parse_number("1234")).to_equal(1234)
```

</details>

#### parses hex with 0x prefix

- parses hex with 0x prefix
- Verify: parses hex with 0x prefix
   - Expected: ld_parse_number("0x1000") equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex with 0x prefix")
step("Verify: parses hex with 0x prefix")
expect(ld_parse_number("0x1000")).to_equal(4096)
```

</details>

#### parses hex uppercase digits

- parses hex uppercase digits
- Verify: parses hex uppercase digits
   - Expected: ld_parse_number("0xAB") equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex uppercase digits")
step("Verify: parses hex uppercase digits")
expect(ld_parse_number("0xAB")).to_equal(171)
```

</details>

#### parses K suffix as 1024 multiplier

- parses K suffix as 1024 multiplier
- Verify: parses K suffix as 1024 multiplier
   - Expected: ld_parse_number("256K") equals `262144`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses K suffix as 1024 multiplier")
step("Verify: parses K suffix as 1024 multiplier")
expect(ld_parse_number("256K")).to_equal(262144)
```

</details>

#### parses M suffix as 1048576 multiplier

- parses M suffix as 1048576 multiplier
- Verify: parses M suffix as 1048576 multiplier
   - Expected: ld_parse_number("1M") equals `1048576`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses M suffix as 1048576 multiplier")
step("Verify: parses M suffix as 1048576 multiplier")
expect(ld_parse_number("1M")).to_equal(1048576)
```

</details>

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: ld_parse_number("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(ld_parse_number("")).to_equal(0)
```

</details>

#### parses zero

- parses zero
- Verify: parses zero
   - Expected: ld_parse_number("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
step("Verify: parses zero")
expect(ld_parse_number("0")).to_equal(0)
```

</details>

### linker_script - tokenizer

#### tokenizes ENTRY(_start) into 5 tokens

- tokenizes ENTRY(_start) into 5 tokens
- Verify: tokenizes ENTRY(_start) into 5 tokens
   - Expected: tokens.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes ENTRY(_start) into 5 tokens")
step("Verify: tokenizes ENTRY(_start) into 5 tokens")
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### first token is Word ENTRY

- first token is Word ENTRY
- Verify: first token is Word ENTRY
   - Expected: tokens[0].kind equals `LdTokenKind.Word`
   - Expected: tokens[0].value equals `ENTRY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first token is Word ENTRY")
step("Verify: first token is Word ENTRY")
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens[0].kind).to_equal(LdTokenKind.Word)
expect(tokens[0].value).to_equal("ENTRY")
```

</details>

#### produces correct token sequence for ENTRY(_start)

- produces correct token sequence for ENTRY(_start)
- Verify: produces correct token sequence for ENTRY(_start)
   - Expected: tokens[1].kind equals `LdTokenKind.LParen`
   - Expected: tokens[2].kind equals `LdTokenKind.Word`
   - Expected: tokens[2].value equals `_start`
   - Expected: tokens[3].kind equals `LdTokenKind.RParen`
   - Expected: tokens[4].kind equals `LdTokenKind.Eof`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct token sequence for ENTRY(_start)")
step("Verify: produces correct token sequence for ENTRY(_start)")
val tokens = ld_tokenize("ENTRY(_start)")
expect(tokens[1].kind).to_equal(LdTokenKind.LParen)
expect(tokens[2].kind).to_equal(LdTokenKind.Word)
expect(tokens[2].value).to_equal("_start")
expect(tokens[3].kind).to_equal(LdTokenKind.RParen)
expect(tokens[4].kind).to_equal(LdTokenKind.Eof)
```

</details>

#### tokenizes empty string to single Eof

- tokenizes empty string to single Eof
- Verify: tokenizes empty string to single Eof
   - Expected: tokens.len() equals `1`
   - Expected: tokens[0].kind equals `LdTokenKind.Eof`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes empty string to single Eof")
step("Verify: tokenizes empty string to single Eof")
val tokens = ld_tokenize("")
expect(tokens.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(tokens[0].kind).to_equal(LdTokenKind.Eof)
```

</details>

#### skips block comments

- skips block comments
- Verify: skips block comments
   - Expected: tokens[0].value equals `ENTRY`
   - Expected: tokens[2].value equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips block comments")
step("Verify: skips block comments")
val tokens = ld_tokenize("/* comment */ ENTRY(x)")
# Should have Word(ENTRY), LParen, Word(x), RParen, Eof
expect(tokens[0].value).to_equal("ENTRY")
expect(tokens[2].value).to_equal("x")
```

</details>

#### tokenizes hex number as Number kind

- tokenizes hex number as Number kind
- Verify: tokenizes hex number as Number kind
   - Expected: tokens[0].kind equals `LdTokenKind.Number`
   - Expected: tokens[0].value equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes hex number as Number kind")
step("Verify: tokenizes hex number as Number kind")
val tokens = ld_tokenize("0x1000")
expect(tokens[0].kind).to_equal(LdTokenKind.Number)
expect(tokens[0].value).to_equal("0x1000")
```

</details>

### linker_script - ENTRY directive

#### parses ENTRY(_start)

- parses ENTRY(_start)
- Verify: parses ENTRY(_start)
   - Expected: script.entry equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ENTRY(_start)")
step("Verify: parses ENTRY(_start)")
val script = ld_parse("ENTRY(_start)").unwrap()
expect(script.entry).to_equal("_start")
```

</details>

#### parses ENTRY(main)

- parses ENTRY(main)
- Verify: parses ENTRY(main)
   - Expected: script.entry equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ENTRY(main)")
step("Verify: parses ENTRY(main)")
val script = ld_parse("ENTRY(main)").unwrap()
expect(script.entry).to_equal("main")
```

</details>

#### ld_has_entry returns true for parsed script

- ld_has_entry returns true for parsed script
- Verify: ld_has_entry returns true for parsed script
   - Expected: ld_has_entry(script) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_has_entry returns true for parsed script")
step("Verify: ld_has_entry returns true for parsed script")
val script = ld_parse("ENTRY(_start)").unwrap()
expect(ld_has_entry(script)).to_equal(true)
```

</details>

### linker_script - MEMORY block

#### parses two memory regions

- parses two memory regions
- Verify: parses two memory regions
   - Expected: ld_region_count(script) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses two memory regions")
step("Verify: parses two memory regions")
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(ld_region_count(script)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### first region is FLASH with rx attrs

- first region is FLASH with rx attrs
- Verify: first region is FLASH with rx attrs
   - Expected: script.memory[0].name equals `FLASH`
   - Expected: script.memory[0].attrs equals `rx`
   - Expected: script.memory[0].origin equals `134217728`
   - Expected: script.memory[0].length equals `262144`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first region is FLASH with rx attrs")
step("Verify: first region is FLASH with rx attrs")
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(script.memory[0].name).to_equal("FLASH")
expect(script.memory[0].attrs).to_equal("rx")
expect(script.memory[0].origin).to_equal(134217728)  # oracle: 134217728 — named expected value from the requirement
expect(script.memory[0].length).to_equal(262144)  # oracle: 262144 — named expected value from the requirement
```

</details>

#### second region is RAM with rwx attrs

- second region is RAM with rwx attrs
- Verify: second region is RAM with rwx attrs
   - Expected: script.memory[1].name equals `RAM`
   - Expected: script.memory[1].attrs equals `rwx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second region is RAM with rwx attrs")
step("Verify: second region is RAM with rwx attrs")
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K }"
val script = ld_parse(input).unwrap()
expect(script.memory[1].name).to_equal("RAM")
expect(script.memory[1].attrs).to_equal("rwx")
```

</details>

#### ld_find_region finds existing region

- ld_find_region finds existing region
- Verify: ld_find_region finds existing region
   - Expected: region != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_find_region finds existing region")
step("Verify: ld_find_region finds existing region")
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K }"
val script = ld_parse(input).unwrap()
val region = ld_find_region(script, "FLASH")
expect(region != nil).to_equal(true)
```

</details>

#### ld_find_region returns nil for nonexistent region

- ld_find_region returns nil for nonexistent region
- Verify: ld_find_region returns nil for nonexistent region


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_find_region returns nil for nonexistent region")
step("Verify: ld_find_region returns nil for nonexistent region")
val input = "MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K }"
val script = ld_parse(input).unwrap()
val region = ld_find_region(script, "NONEXIST")
expect(region).to_be_nil()
```

</details>

### linker_script - SECTIONS block

#### parses three output sections

- parses three output sections
- Verify: parses three output sections
   - Expected: ld_section_count(script) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses three output sections")
step("Verify: parses three output sections")
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH .data : { *(.data) } > RAM .bss : { *(.bss) } > RAM }"
val script = ld_parse(input).unwrap()
expect(ld_section_count(script)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### first section is .text with FLASH region

- first section is .text with FLASH region
- Verify: first section is .text with FLASH region
   - Expected: script.sections[0].name equals `.text`
   - Expected: script.sections[0].region equals `FLASH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first section is .text with FLASH region")
step("Verify: first section is .text with FLASH region")
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH .data : { *(.data) } > RAM }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].name).to_equal(".text")
expect(script.sections[0].region).to_equal("FLASH")
```

</details>

#### first section has two input patterns

- first section has two input patterns
- Verify: first section has two input patterns
   - Expected: script.sections[0].inputs.len() equals `2`
   - Expected: script.sections[0].inputs[0].pattern equals `.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first section has two input patterns")
step("Verify: first section has two input patterns")
val input = "SECTIONS { .text : { *(.text) *(.text*) } > FLASH }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].inputs.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(script.sections[0].inputs[0].pattern).to_equal(".text")
```

</details>

#### ld_find_section finds existing section

- ld_find_section finds existing section
- Verify: ld_find_section finds existing section
   - Expected: section != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_find_section finds existing section")
step("Verify: ld_find_section finds existing section")
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
val section = ld_find_section(script, ".text")
expect(section != nil).to_equal(true)
```

</details>

#### ld_find_section returns nil for nonexistent section

- ld_find_section returns nil for nonexistent section
- Verify: ld_find_section returns nil for nonexistent section


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_find_section returns nil for nonexistent section")
step("Verify: ld_find_section returns nil for nonexistent section")
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
val section = ld_find_section(script, ".nonexist")
expect(section).to_be_nil()
```

</details>

### linker_script - complete script

#### parses full script with ENTRY, MEMORY, and SECTIONS

- parses full script with ENTRY, MEMORY, and SECTIONS
- Verify: parses full script with ENTRY, MEMORY, and SECTIONS
   - Expected: script.entry equals `_start`
   - Expected: ld_region_count(script) equals `2`
   - Expected: ld_section_count(script) equals `2`
   - Expected: ld_has_entry(script) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses full script with ENTRY, MEMORY, and SECTIONS")
step("Verify: parses full script with ENTRY, MEMORY, and SECTIONS")
val input = "ENTRY(_start) MEMORY { FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 256K RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 64K } SECTIONS { .text : { *(.text) } > FLASH .data : { *(.data) } > RAM }"
val script = ld_parse(input).unwrap()
expect(script.entry).to_equal("_start")
expect(ld_region_count(script)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ld_section_count(script)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ld_has_entry(script)).to_equal(true)
```

</details>

### linker_script - convenience functions

#### ld_script_new creates empty script

- ld_script_new creates empty script
- Verify: ld_script_new creates empty script
   - Expected: script.entry equals ``
   - Expected: ld_section_count(script) equals `0`
   - Expected: ld_region_count(script) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_script_new creates empty script")
step("Verify: ld_script_new creates empty script")
val script = ld_script_new()
expect(script.entry).to_equal("")
expect(ld_section_count(script)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ld_region_count(script)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### ld_has_entry returns false for empty script

- ld_has_entry returns false for empty script
- Verify: ld_has_entry returns false for empty script
   - Expected: ld_has_entry(script) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld_has_entry returns false for empty script")
step("Verify: ld_has_entry returns false for empty script")
val script = ld_script_new()
expect(ld_has_entry(script)).to_equal(false)
```

</details>

### linker_script - section with explicit address

#### parses section with explicit address

- parses section with explicit address
- Verify: parses section with explicit address
   - Expected: script.sections[0].address equals `134217728`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses section with explicit address")
step("Verify: parses section with explicit address")
val input = "SECTIONS { .isr_vector 0x08000000 : { *(.isr_vector) } }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].address).to_equal(134217728)  # oracle: 134217728 — named expected value from the requirement
```

</details>

#### section without address has address -1

- section without address has address -1
- Verify: section without address has address -1
   - Expected: script.sections[0].address equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("section without address has address -1")
step("Verify: section without address has address -1")
val input = "SECTIONS { .text : { *(.text) } > FLASH }"
val script = ld_parse(input).unwrap()
expect(script.sections[0].address).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-BACKEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42edee90759136093af971a9d73a87f9c79197b9b2de7149325cab3b396ea0cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42edee90759136093af971a9d73a87f9c79197b9b2de7149325cab3b396ea0cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42edee90759136093af971a9d73a87f9c79197b9b2de7149325cab3b396ea0cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/linker/linker_script_spec.spl
mirror: doc/06_spec/unit/compiler/backend/linker/linker_script_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/linker/linker_script_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/linker/linker_script_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/linker/linker_script_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/linker/linker_script_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses decimal number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/linker/linker_script_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses hex with 0x prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/linker/linker_script_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses hex uppercase digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
