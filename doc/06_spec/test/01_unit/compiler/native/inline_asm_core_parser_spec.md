# Inline Asm Core Parser Specification

> <details>

<!-- sdn-diagram:id=inline_asm_core_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_asm_core_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_asm_core_parser_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_asm_core_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Asm Core Parser Specification

## Scenarios

### Core parser raw asm blocks

#### preserves unquoted x86 instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_text("fn test():\n    asm { cli }\n")).to_equal("cli")
```

</details>

#### preserves ARM immediate hash text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_text("fn test():\n    asm volatile { bkpt #0 }\n")).to_equal("bkpt #0")
```

</details>

#### preserves RISC-V comma operands

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_text("fn test():\n    asm { fence rw, rw }\n")).to_equal("fence rw, rw")
```

</details>

#### normalizes multiple lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = parse_first_asm_text("fn test():\n    asm {\n        cli\n        hlt\n    }\n")
expect(text).to_equal("cli\nhlt")
```

</details>

#### keeps quoted braced lines compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_text("fn test():\n    asm { \"nop\" }\n")).to_equal("nop")
```

</details>

#### does not warn for canonical braced asm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_warning_count("fn test():\n    asm { nop }\n")).to_equal(0)
```

</details>

#### warns for legacy parenthesized asm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_warning_count("fn test():\n    asm(\"nop\")\n")).to_equal(1)
```

</details>

#### warns for legacy bare string asm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_warning_count("fn test():\n    asm \"nop\"\n")).to_equal(1)
```

</details>

#### warns for legacy colon string asm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_warning_count("fn test():\n    asm: \"nop\"\n")).to_equal(1)
```

</details>

#### warns for legacy colon block asm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_first_asm_warning_count("fn test():\n    asm:\n        \"nop\"\n")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/inline_asm_core_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Core parser raw asm blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
