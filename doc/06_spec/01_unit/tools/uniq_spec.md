# Uniq Specification

> <details>

<!-- sdn-diagram:id=uniq_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=uniq_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

uniq_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=uniq_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Uniq Specification

## Scenarios

### uniq tool

#### line comparison

#### detects equal lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lines_equal("hello", "hello", false)
expect(result).to_equal(true)
```

</details>

#### detects different lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lines_equal("hello", "world", false)
expect(result).to_equal(false)
```

</details>

#### compares case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lines_equal("Hello", "hello", true)
expect(result).to_equal(true)
```

</details>

#### rejects different lines case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lines_equal("Hello", "World", true)
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/uniq_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- uniq tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
