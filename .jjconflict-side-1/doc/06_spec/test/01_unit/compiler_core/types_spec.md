# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### Types

#### keeps core string span token and symbol helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = types_source()

expect(source).to_contain("fn str_concat(a: text, b: text) -> text")
expect(source).to_contain("fn str_contains(s: text, needle: text) -> bool")
expect(source).to_contain("fn span_new(start: i64, end_pos: i64, line: i64, col: i64) -> i64")
expect(source).to_contain("fn token_new(kind: i64, span_id: i64, value: text) -> i64")
expect(source).to_contain("fn symbol_new(name: text, sym_type: i64, depth: i64, decl_id: i64, is_mut: i64) -> i64")
expect(source).to_contain("fn scope_push() -> i64")
```

</details>

#### keeps type tags and type name conversion available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = types_source()

expect(source).to_contain("val TYPE_VOID = 0")
expect(source).to_contain("val TYPE_BOOL = 1")
expect(source).to_contain("val TYPE_I64 = 2")
expect(source).to_contain("val TYPE_OPTION = 14")
expect(source).to_contain("val TYPE_RESULT = 19")
expect(source).to_contain("val TYPE_FUTURE = 20")
expect(source).to_contain("fn type_tag_name(tag: i64) -> text")
expect(source).to_contain("fn type_tag_to_c(tag: i64) -> text")
```

</details>

#### keeps named type and function signature registries available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = types_source()

expect(source).to_contain("fn named_type_register(name: text, field_names: [text], field_types: [i64]) -> i64")
expect(source).to_contain("fn named_type_find(name: text) -> i64")
expect(source).to_contain("fn named_type_field_type_tags(type_id: i64) -> [i64]")
expect(source).to_contain("fn fn_sig_register(name: text, param_names: [text], param_types: [i64], ret_type: i64, is_ext: i64) -> i64")
expect(source).to_contain("fn fn_sig_find(name: text) -> i64")
expect(source).to_contain("fn reset_all_pools()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/types_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
