# Keyof Specification

> <details>

<!-- sdn-diagram:id=keyof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=keyof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

keyof_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=keyof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keyof Specification

## Scenarios

### keyof T Operator

#### parses keyof as fields traits sugar

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/parser_primary_part2.spl")

expect(src).to_contain("# keyof T -- compile-time field name list")
expect(src).to_contain("if par_check(TOK_KW_KEYOF):")
expect(src).to_contain("keyof_args.push(expr_string_lit(\"fields\", 0))")
expect(src).to_contain("keyof_args.push(expr_string_lit(keyof_type, 0))")
expect(src).to_contain("val keyof_callee = expr_ident(\"__traits\", 0)")
expect(src).to_contain("return expr_call(keyof_callee, keyof_args, 0)")
```

</details>

#### documents runtime equivalent intrinsics

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_sync_mut/intrinsics.spl")

expect(src).to_contain("# ## keyof Operator")
expect(src).to_contain("#   keyof T")
expect(src).to_contain("fn keyof_fields(type_name: text) -> [text]:")
expect(src).to_contain("fn has_field(type_name: text, field_name: text) -> bool:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/keyof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- keyof T Operator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
