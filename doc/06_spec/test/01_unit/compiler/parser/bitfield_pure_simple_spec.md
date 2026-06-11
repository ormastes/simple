# Bitfield Pure Simple Specification

> <details>

<!-- sdn-diagram:id=bitfield_pure_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_pure_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_pure_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_pure_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Pure Simple Specification

## Scenarios

### Bitfield Pure Simple Implementation

#### registers bitfield keyword in token table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = read_text("src/compiler/10.frontend/core/tokens.spl")
expect(tokens.contains("TOK_KW_BITFIELD")).to_equal(true)
expect(tokens.contains("if name == \"bitfield\": return TOK_KW_BITFIELD")).to_equal(true)
expect(tokens.contains("if kind == TOK_KW_BITFIELD: return \"bitfield\"")).to_equal(true)
```

</details>

#### routes module declarations to parse_bitfield_decl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls2 = read_text("src/compiler/10.frontend/core/parser_decls_part2.spl")
expect(decls2.contains("parse_bitfield_decl()")).to_equal(true)
```

</details>

#### supports backing type and reserved underscore fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls3 = read_text("src/compiler/10.frontend/core/parser_decls_part3.spl")
expect(decls3.contains("val backing_type = parser_parse_type()")).to_equal(true)
expect(decls3.contains("val is_underscore: bool")).to_equal(true)
```

</details>

#### enforces backing and field width validation in parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls3 = read_text("src/compiler/10.frontend/core/parser_decls_part3.spl")
expect(decls3.contains("bitfield backing type must be u8, u16, u32, or u64")).to_equal(true)
expect(decls3.contains("bitfield field type must be bool, uN, or iN")).to_equal(true)
expect(decls3.contains("int_to_str(used_bits)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/bitfield_pure_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bitfield Pure Simple Implementation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
