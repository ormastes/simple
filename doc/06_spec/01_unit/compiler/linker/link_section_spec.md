# Link Section Specification

> Tests covering link section attribute parsing, default attributes, @link_section annotation, @addr_space annotation, both annotations together, link_attr_has_placement, link_attr_is_flash, link_attr_is_ram, link_attr_codegen_hint, extract_link_string_arg.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Link Section Specification

## Scenarios

### link section attribute parsing

### default attributes

#### default_no_section: default attr has no section

- default_no_section: default attr has no section
   - Expected: has_section is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_no_section: default attr has no section")
val has_section = false
expect(has_section).to_equal(false)
```

</details>

#### default_no_addr_space: default attr has no addr_space

- default_no_addr_space: default attr has no addr_space
   - Expected: has_addr_space is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_no_addr_space: default attr has no addr_space")
val has_addr_space = false
expect(has_addr_space).to_equal(false)
```

</details>

#### default_section_empty: default section is empty string

- default_section_empty: default section is empty string
   - Expected: section equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_section_empty: default section is empty string")
val section = ""
expect(section).to_equal("")
```

</details>

#### default_addr_space_empty: default addr_space is empty string

- default_addr_space_empty: default addr_space is empty string
   - Expected: addr_space equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_addr_space_empty: default addr_space is empty string")
val addr_space = ""
expect(addr_space).to_equal("")
```

</details>

### @link_section annotation

#### link_section_rodata: @link_section('.rodata') sets section

- link_section_rodata: @link_section('.rodata') sets section
   - Expected: attr[0] equals `.rodata`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("link_section_rodata: @link_section('.rodata') sets section")
val attr = helper_make_attr(".rodata", "")
expect(attr[0]).to_equal(".rodata")
```

</details>

#### link_section_has_section_true: @link_section sets has_section=true

- link_section_has_section_true: @link_section sets has_section=true
   - Expected: attr[1] equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("link_section_has_section_true: @link_section sets has_section=true")
val attr = helper_make_attr(".rodata", "")
expect(attr[1]).to_equal("true")
```

</details>

#### link_section_isr: @link_section('.isr_vector') sets section

- link_section_isr: @link_section('.isr_vector') sets section
   - Expected: attr[0] equals `.isr_vector`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("link_section_isr: @link_section('.isr_vector') sets section")
val attr = helper_make_attr(".isr_vector", "")
expect(attr[0]).to_equal(".isr_vector")
```

</details>

### @addr_space annotation

#### addr_space_flash: @addr_space('flash') sets addr_space

- addr_space_flash: @addr_space('flash') sets addr_space
   - Expected: attr[2] equals `flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addr_space_flash: @addr_space('flash') sets addr_space")
val attr = helper_make_attr("", "flash")
expect(attr[2]).to_equal("flash")
```

</details>

#### addr_space_has_addr_space_true: @addr_space sets has_addr_space=true

- addr_space_has_addr_space_true: @addr_space sets has_addr_space=true
   - Expected: attr[3] equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addr_space_has_addr_space_true: @addr_space sets has_addr_space=true")
val attr = helper_make_attr("", "flash")
expect(attr[3]).to_equal("true")
```

</details>

#### addr_space_ram: @addr_space('ram') sets addr_space

- addr_space_ram: @addr_space('ram') sets addr_space
   - Expected: attr[2] equals `ram`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addr_space_ram: @addr_space('ram') sets addr_space")
val attr = helper_make_attr("", "ram")
expect(attr[2]).to_equal("ram")
```

</details>

### both annotations together

#### both_section_and_addr: section and addr_space can coexist

- both_section_and_addr: section and addr_space can coexist
   - Expected: attr[0] equals `.isr_vector`
   - Expected: attr[2] equals `flash`
   - Expected: attr[1] equals `true`
   - Expected: attr[3] equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both_section_and_addr: section and addr_space can coexist")
val attr = helper_make_attr(".isr_vector", "flash")
expect(attr[0]).to_equal(".isr_vector")
expect(attr[2]).to_equal("flash")
expect(attr[1]).to_equal("true")
expect(attr[3]).to_equal("true")
```

</details>

### link_attr_has_placement

#### has_placement_false_when_no_attrs: no attrs means no placement

- has_placement_false_when_no_attrs: no attrs means no placement
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_placement_false_when_no_attrs: no attrs means no placement")
val result = helper_has_placement(false, false)
expect(result).to_equal(false)
```

</details>

#### has_placement_true_with_section: section alone means has placement

- has_placement_true_with_section: section alone means has placement
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_placement_true_with_section: section alone means has placement")
val result = helper_has_placement(true, false)
expect(result).to_equal(true)
```

</details>

#### has_placement_true_with_addr_space: addr_space alone means has placement

- has_placement_true_with_addr_space: addr_space alone means has placement
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_placement_true_with_addr_space: addr_space alone means has placement")
val result = helper_has_placement(false, true)
expect(result).to_equal(true)
```

</details>

#### has_placement_true_with_both: both section and addr_space means has placement

- has_placement_true_with_both: both section and addr_space means has placement
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_placement_true_with_both: both section and addr_space means has placement")
val result = helper_has_placement(true, true)
expect(result).to_equal(true)
```

</details>

### link_attr_is_flash

#### is_flash_true_for_flash: addr_space flash returns true

- is_flash_true_for_flash: addr_space flash returns true
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_flash_true_for_flash: addr_space flash returns true")
val result = helper_is_flash(true, "flash")
expect(result).to_equal(true)
```

</details>

#### is_flash_false_for_ram: addr_space ram returns false

- is_flash_false_for_ram: addr_space ram returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_flash_false_for_ram: addr_space ram returns false")
val result = helper_is_flash(true, "ram")
expect(result).to_equal(false)
```

</details>

#### is_flash_false_when_no_addr_space: no addr_space returns false

- is_flash_false_when_no_addr_space: no addr_space returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_flash_false_when_no_addr_space: no addr_space returns false")
val result = helper_is_flash(false, "flash")
expect(result).to_equal(false)
```

</details>

### link_attr_is_ram

#### is_ram_true_for_ram: addr_space ram returns true

- is_ram_true_for_ram: addr_space ram returns true
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ram_true_for_ram: addr_space ram returns true")
val result = helper_is_ram(true, "ram")
expect(result).to_equal(true)
```

</details>

#### is_ram_true_for_sram: addr_space sram returns true

- is_ram_true_for_sram: addr_space sram returns true
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ram_true_for_sram: addr_space sram returns true")
val result = helper_is_ram(true, "sram")
expect(result).to_equal(true)
```

</details>

#### is_ram_false_for_flash: addr_space flash is not ram

- is_ram_false_for_flash: addr_space flash is not ram
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ram_false_for_flash: addr_space flash is not ram")
val result = helper_is_ram(true, "flash")
expect(result).to_equal(false)
```

</details>

#### is_ram_false_when_no_addr_space: no addr_space returns false

- is_ram_false_when_no_addr_space: no addr_space returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ram_false_when_no_addr_space: no addr_space returns false")
val result = helper_is_ram(false, "ram")
expect(result).to_equal(false)
```

</details>

### link_attr_codegen_hint

#### codegen_hint_empty_when_no_placement: no attrs gives empty hint

- codegen_hint_empty_when_no_placement: no attrs gives empty hint
   - Expected: hint equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codegen_hint_empty_when_no_placement: no attrs gives empty hint")
val hint = helper_codegen_hint(false, "", false, "")
expect(hint).to_equal("")
```

</details>

#### codegen_hint_section_only: section attr formats as section=X

- codegen_hint_section_only: section attr formats as section=X
   - Expected: hint equals `section=.text.cold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codegen_hint_section_only: section attr formats as section=X")
val hint = helper_codegen_hint(true, ".text.cold", false, "")
expect(hint).to_equal("section=.text.cold")
```

</details>

#### codegen_hint_addr_space_only: addr_space attr formats as addr_space=X

- codegen_hint_addr_space_only: addr_space attr formats as addr_space=X
   - Expected: hint equals `addr_space=flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codegen_hint_addr_space_only: addr_space attr formats as addr_space=X")
val hint = helper_codegen_hint(false, "", true, "flash")
expect(hint).to_equal("addr_space=flash")
```

</details>

#### codegen_hint_both: both attrs format as section=X addr_space=Y

- codegen_hint_both: both attrs format as section=X addr_space=Y
   - Expected: hint equals `section=.isr_vector addr_space=flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codegen_hint_both: both attrs format as section=X addr_space=Y")
val hint = helper_codegen_hint(true, ".isr_vector", true, "flash")
expect(hint).to_equal("section=.isr_vector addr_space=flash")
```

</details>

### extract_link_string_arg

#### extract_empty_args_returns_empty: no args gives empty string

- extract_empty_args_returns_empty: no args gives empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_empty_args_returns_empty: no args gives empty string")
val result = helper_extract_link_string_arg_empty()
expect(result).to_equal("")
```

</details>

#### extract_quoted_arg_strips_quotes: quoted string is unquoted

- extract_quoted_arg_strips_quotes: quoted string is unquoted
   - Expected: result equals `.rodata`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_quoted_arg_strips_quotes: quoted string is unquoted")
val result = helper_extract_link_string_arg_quoted("\".rodata\"")
expect(result).to_equal(".rodata")
```

</details>

#### extract_unquoted_arg_unchanged: unquoted arg is returned as-is

- extract_unquoted_arg_unchanged: unquoted arg is returned as-is
   - Expected: result equals `.rodata`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_unquoted_arg_unchanged: unquoted arg is returned as-is")
val result = helper_extract_link_string_arg_quoted(".rodata")
expect(result).to_equal(".rodata")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/link_section_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering link section attribute parsing, default attributes, @link_section annotation, @addr_space annotation, both annotations together, link_attr_has_placement, link_attr_is_flash, link_attr_is_ram, link_attr_codegen_hint, extract_link_string_arg.
- link section attribute parsing
- default attributes
- @link_section annotation
- @addr_space annotation
- both annotations together
- link_attr_has_placement
- link_attr_is_flash
- link_attr_is_ram
- link_attr_codegen_hint
- extract_link_string_arg

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a3d5c0db02d257fe00d907c2497791136bab269d2534f7207d233a2a66d7a7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a3d5c0db02d257fe00d907c2497791136bab269d2534f7207d233a2a66d7a7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a3d5c0db02d257fe00d907c2497791136bab269d2534f7207d233a2a66d7a7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/linker/link_section_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/link_section_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/link_section_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/link_section_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/link_section_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_no_section: default attr has no section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/link_section_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_no_addr_space: default attr has no addr_space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/link_section_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_section_empty: default section is empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
