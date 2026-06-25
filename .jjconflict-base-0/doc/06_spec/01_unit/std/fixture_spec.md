# Fixture Specification

> <details>

<!-- sdn-diagram:id=fixture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixture_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixture Specification

## Scenarios

### Fixture Tests

### using test data

#### tests with fixture value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_value = 42
expect fixture_value == 42
```

</details>

#### tests with fixture string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_name = "test_user"
expect fixture_name == "test_user"
```

</details>

#### tests with fixture list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_list = [1, 2, 3]
expect fixture_list[0] == 1
expect fixture_list[1] == 2
expect fixture_list[2] == 3
```

</details>

### computed fixtures

#### uses computed test data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 10
val multiplier = 5
val expected = base * multiplier
expect expected == 50
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/fixture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fixture Tests
- using test data
- computed fixtures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
