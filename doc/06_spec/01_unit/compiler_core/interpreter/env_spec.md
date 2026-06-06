# Env Specification

> <details>

<!-- sdn-diagram:id=env_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=env_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

env_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=env_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Specification

## Scenarios

### Env

#### keeps scope environment operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_env_source()

expect(source).to_contain("fn env_init()")
expect(source).to_contain("fn env_reset()")
expect(source).to_contain("fn env_push_scope()")
expect(source).to_contain("fn env_pop_scope()")
expect(source).to_contain("fn env_scope_depth() -> i64")
```

</details>

#### keeps variable and global lookup operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_env_source()

expect(source).to_contain("fn env_define(name: text, value_id: i64)")
expect(source).to_contain("fn env_assign(name: text, value_id: i64) -> bool")
expect(source).to_contain("fn env_lookup(name: text) -> i64")
expect(source).to_contain("fn env_define_global(name: text, value_id: i64)")
expect(source).to_contain("fn env_lookup_global(name: text) -> i64")
expect(source).to_contain("fn env_remove_global(name: text) -> bool")
```

</details>

#### keeps frame local operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_env_source()

expect(source).to_contain("fn env_push_frame(local_count: i64)")
expect(source).to_contain("fn env_pop_frame()")
expect(source).to_contain("fn env_get_local(slot: i64) -> i64")
expect(source).to_contain("fn env_set_local(slot: i64, value_id: i64)")
expect(source).to_contain("fn env_has_frame() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/env_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Env

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
