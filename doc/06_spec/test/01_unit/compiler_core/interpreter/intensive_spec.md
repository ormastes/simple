# Intensive Specification

> <details>

<!-- sdn-diagram:id=intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intensive Specification

## Scenarios

### Intensive

#### keeps intensive value coverage targets present in the maintained source

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = core_interpreter_source("value.spl")

expect(source).to_contain("fn val_is_truthy")
expect(source).to_contain("fn val_struct_get_field")
expect(source).to_contain("fn val_struct_set_field")
expect(source).to_contain("fn val_to_text")
expect(source).to_contain("fn core_val_make_int")
expect(source).to_contain("fn core_val_get_string")
```

</details>

#### keeps intensive environment coverage targets present in the maintained source

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = core_interpreter_source("env.spl")

expect(source).to_contain("fn env_define(name: text, value_id: i64)")
expect(source).to_contain("fn env_assign(name: text, value_id: i64) -> bool")
expect(source).to_contain("fn env_define_global(name: text, value_id: i64)")
expect(source).to_contain("fn env_lookup_global(name: text) -> i64")
expect(source).to_contain("fn env_push_frame(local_count: i64)")
expect(source).to_contain("fn env_pop_scope()")
```

</details>

#### keeps intensive operations coverage targets present in the maintained source

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = core_interpreter_source("ops.spl")

expect(source).to_contain("fn val_add(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_sub(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_mul(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_div(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_mod(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_binary_op(op: i64, a: i64, b: i64) -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
