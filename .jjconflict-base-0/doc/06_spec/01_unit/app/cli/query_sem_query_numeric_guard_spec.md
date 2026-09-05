# Query Sem Query Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=query_sem_query_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_sem_query_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_sem_query_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_sem_query_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Sem Query Numeric Guard Specification

## Scenarios

### semantic query numeric guard

#### rejects invalid integer predicates without direct parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_sem_query.spl") ?? ""

expect(source).to_contain("val expected_opt = expected_str.to_int()")
expect(source).to_contain("if expected_opt == nil:")
expect(source).to_contain("return false")
expect(source.contains("val expected = expected_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_sem_query_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semantic query numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
