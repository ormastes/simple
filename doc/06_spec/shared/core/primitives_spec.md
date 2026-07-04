# Primitives Specification

> <details>

<!-- sdn-diagram:id=primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitives_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitives Specification

## Scenarios

### Primitives

### integers

#### handles positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(40 + 2).to_equal(42)
```

</details>

#### handles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(7 - 7).to_equal(0)
```

</details>

#### handles negative with parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(0 - 1).to_equal(-1)
```

</details>

### booleans

#### handles true

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not true:
    fail("true should be truthy")
```

</details>

#### handles false

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if false:
    fail("false should not be truthy")
```

</details>

#### negates correctly

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not (not false):
    fail("not false should be truthy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/core/primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Primitives
- integers
- booleans

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
