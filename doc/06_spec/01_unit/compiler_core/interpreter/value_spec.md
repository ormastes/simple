# Value Specification

> <details>

<!-- sdn-diagram:id=value_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=value_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

value_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=value_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Value Specification

## Scenarios

### Value

#### keeps interpreter value kind constants and constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_value_source()

expect(source).to_contain("val VAL_NIL: i64 = 0")
expect(source).to_contain("val VAL_BOOL: i64 = 1")
expect(source).to_contain("val VAL_INT: i64 = 2")
expect(source).to_contain("val VAL_TEXT: i64 = 4")
expect(source).to_contain("fn val_make_nil() -> i64")
expect(source).to_contain("fn val_make_bool(b: bool) -> i64")
expect(source).to_contain("fn val_make_int(n: i64) -> i64")
expect(source).to_contain("fn val_make_text(s: text) -> i64")
```

</details>

#### keeps interpreter value accessors and predicates available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_value_source()

expect(source).to_contain("fn val_get_kind(vid: i64) -> i64")
expect(source).to_contain("fn val_get_int(vid: i64) -> i64")
expect(source).to_contain("fn val_get_bool(vid: i64) -> bool")
expect(source).to_contain("fn val_get_text(vid: i64) -> text")
expect(source).to_contain("fn val_is_truthy(vid: i64) -> bool")
expect(source).to_contain("fn val_to_text(vid: i64) -> text")
expect(source).to_contain("fn val_equals(a: i64, b: i64) -> bool")
```

</details>

#### uses the canonical value-kind accessor in type checking

The source helper reads `src/compiler/10.frontend/core/type_checker.spl`.
The scenario requires the canonical arena import and actual accessor calls,
and rejects obsolete `val_kind(` references.

```simple
val source = value_kind_consumers_source()
expect(source).to_contain("use compiler.core.interpreter.value.{val_get_kind, val_get_int, val_get_float, val_get_text}")
expect(source).to_contain("val kind = val_get_kind(value_id)")
expect(source.contains("val_kind(")).to_equal(false)
```

Stage 1 diagnostic on release base `475c2f918db` executed all four examples:
4 passed, 0 failed, 0 skipped, 0 dropped. The cached bootstrap producer SHA-256
was `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`.
Pure Simple runtime qualification remains pending because the release binary
is unavailable on this host. No compiler rebuild was performed.

#### keeps struct and thunk value support available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_value_source()

expect(source).to_contain("fn val_make_struct(type_name: text, field_names: [text], field_values: [i64]) -> i64")
expect(source).to_contain("fn val_struct_get_field(vid: i64, field_name: text) -> i64")
expect(source).to_contain("fn val_struct_set_field(vid: i64, field_name: text, new_val: i64)")
expect(source).to_contain("fn val_make_thunk(expr_id: i64) -> i64")
expect(source).to_contain("fn val_is_thunk(vid: i64) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/value_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Value

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
