# Database Test Extended Specification

> <details>

<!-- sdn-diagram:id=database_test_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_test_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_test_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_test_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Test Extended Specification

## Scenarios

### Database Test Extended

#### keeps extended test database exports available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = test_extended_main_source()

expect(source).to_contain("Test Database Extended - Main Module")
expect(source).to_contain("TestDatabaseExtended")
expect(source).to_contain("create_test_database_extended")
expect(source).to_contain("load_with_migration")
```

</details>

#### keeps extended test tracking records available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = test_extended_source("types.spl")

expect(source).to_contain("Test Database Extended - Type Definitions")
expect(source).to_contain("struct TimingSummary:")
expect(source).to_contain("struct RunRecord:")
expect(source).to_contain("struct TestInfo:")
```

</details>

#### keeps run management and test result tracking available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = test_extended_source("database.spl")

expect(source).to_contain("Test Database Extended - Main Class")
expect(source).to_contain("class TestDatabaseExtended:")
expect(source).to_contain("test_runs")
expect(source).to_contain("timing_runs")
expect(source).to_contain("update_test_result")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_test_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Database Test Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
