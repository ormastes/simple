# Link Section Specification

> <details>

<!-- sdn-diagram:id=link_section_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=link_section_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

link_section_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=link_section_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_section = false
expect(has_section).to_equal(false)
```

</details>

#### default_no_addr_space: default attr has no addr_space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_addr_space = false
expect(has_addr_space).to_equal(false)
```

</details>

#### default_section_empty: default section is empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section = ""
expect(section).to_equal("")
```

</details>

#### default_addr_space_empty: default addr_space is empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr_space = ""
expect(addr_space).to_equal("")
```

</details>

### @link_section annotation

#### link_section_rodata: @link_section('.rodata') sets section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr(".rodata", "")
expect(attr[0]).to_equal(".rodata")
```

</details>

#### link_section_has_section_true: @link_section sets has_section=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr(".rodata", "")
expect(attr[1]).to_equal("true")
```

</details>

#### link_section_isr: @link_section('.isr_vector') sets section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr(".isr_vector", "")
expect(attr[0]).to_equal(".isr_vector")
```

</details>

### @addr_space annotation

#### addr_space_flash: @addr_space('flash') sets addr_space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr("", "flash")
expect(attr[2]).to_equal("flash")
```

</details>

#### addr_space_has_addr_space_true: @addr_space sets has_addr_space=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr("", "flash")
expect(attr[3]).to_equal("true")
```

</details>

#### addr_space_ram: @addr_space('ram') sets addr_space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr("", "ram")
expect(attr[2]).to_equal("ram")
```

</details>

### both annotations together

#### both_section_and_addr: section and addr_space can coexist

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = helper_make_attr(".isr_vector", "flash")
expect(attr[0]).to_equal(".isr_vector")
expect(attr[2]).to_equal("flash")
expect(attr[1]).to_equal("true")
expect(attr[3]).to_equal("true")
```

</details>

### link_attr_has_placement

#### has_placement_false_when_no_attrs: no attrs means no placement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_has_placement(false, false)
expect(result).to_equal(false)
```

</details>

#### has_placement_true_with_section: section alone means has placement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_has_placement(true, false)
expect(result).to_equal(true)
```

</details>

#### has_placement_true_with_addr_space: addr_space alone means has placement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_has_placement(false, true)
expect(result).to_equal(true)
```

</details>

#### has_placement_true_with_both: both section and addr_space means has placement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_has_placement(true, true)
expect(result).to_equal(true)
```

</details>

### link_attr_is_flash

#### is_flash_true_for_flash: addr_space flash returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_flash(true, "flash")
expect(result).to_equal(true)
```

</details>

#### is_flash_false_for_ram: addr_space ram returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_flash(true, "ram")
expect(result).to_equal(false)
```

</details>

#### is_flash_false_when_no_addr_space: no addr_space returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_flash(false, "flash")
expect(result).to_equal(false)
```

</details>

### link_attr_is_ram

#### is_ram_true_for_ram: addr_space ram returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_ram(true, "ram")
expect(result).to_equal(true)
```

</details>

#### is_ram_true_for_sram: addr_space sram returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_ram(true, "sram")
expect(result).to_equal(true)
```

</details>

#### is_ram_false_for_flash: addr_space flash is not ram

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_ram(true, "flash")
expect(result).to_equal(false)
```

</details>

#### is_ram_false_when_no_addr_space: no addr_space returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_is_ram(false, "ram")
expect(result).to_equal(false)
```

</details>

### link_attr_codegen_hint

#### codegen_hint_empty_when_no_placement: no attrs gives empty hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = helper_codegen_hint(false, "", false, "")
expect(hint).to_equal("")
```

</details>

#### codegen_hint_section_only: section attr formats as section=X

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = helper_codegen_hint(true, ".text.cold", false, "")
expect(hint).to_equal("section=.text.cold")
```

</details>

#### codegen_hint_addr_space_only: addr_space attr formats as addr_space=X

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = helper_codegen_hint(false, "", true, "flash")
expect(hint).to_equal("addr_space=flash")
```

</details>

#### codegen_hint_both: both attrs format as section=X addr_space=Y

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = helper_codegen_hint(true, ".isr_vector", true, "flash")
expect(hint).to_equal("section=.isr_vector addr_space=flash")
```

</details>

### extract_link_string_arg

#### extract_empty_args_returns_empty: no args gives empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_extract_link_string_arg_empty()
expect(result).to_equal("")
```

</details>

#### extract_quoted_arg_strips_quotes: quoted string is unquoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_extract_link_string_arg_quoted("\".rodata\"")
expect(result).to_equal(".rodata")
```

</details>

#### extract_unquoted_arg_unchanged: unquoted arg is returned as-is

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
