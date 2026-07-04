# Class Basics Specification

> Tests that classes with list fields can be created and populated correctly.

<!-- sdn-diagram:id=class_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=class_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

class_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=class_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Basics Specification

Tests that classes with list fields can be created and populated correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Status | In Progress |
| Source | `test/01_unit/app/depgraph/class_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that classes with list fields can be created and populated correctly.

## Scenarios

### Class Basics

#### creates a result with name 'test'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_result()
expect(result.name).to_equal("test")
```

</details>

#### creates a result with 2 items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_result()
expect(result.items.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
