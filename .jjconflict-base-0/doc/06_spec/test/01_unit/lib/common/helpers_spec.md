# Helpers Specification

> <details>

<!-- sdn-diagram:id=helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Specification

## Scenarios

### Helpers

#### keeps the sync facade wired to shared testing helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = testing_helpers_facade_source()

expect(source).to_contain("export use std.gc_async_mut.src.testing.helpers.*")
```

</details>

#### keeps assertion helpers available as free functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = testing_helpers_source()

expect(source).to_contain("pub fn assert_eq<T>(actual: T, expected: T, message: text)")
expect(source).to_contain("pub fn assert_ne<T>(actual: T, unexpected: T, message: text)")
expect(source).to_contain("pub fn assert_true(condition: Condition, message: text)")
expect(source).to_contain("pub fn assert_false(condition: Condition, message: text)")
```

</details>

#### keeps option and result assertion helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = testing_helpers_source()

expect(source).to_contain("pub fn assert_some<T>(option: Option<T>, message: text) -> T")
expect(source).to_contain("pub fn assert_none<T>(option: Option<T>, message: text)")
expect(source).to_contain("pub fn assert_ok<T, E>(result: Result<T, E>, message: text) -> T")
expect(source).to_contain("pub fn assert_err<T, E>(result: Result<T, E>, message: text) -> E")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
