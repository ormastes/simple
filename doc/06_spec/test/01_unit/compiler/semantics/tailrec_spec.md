# Tailrec Specification

> <details>

<!-- sdn-diagram:id=tailrec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tailrec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tailrec_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tailrec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tailrec Specification

## Scenarios

### @tailrec annotation

#### tailrec annotated function works correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# factorial(5) = 120
val result = factorial_tr(5, 1)
expect(result).to_equal(120)
```

</details>

#### tailrec accumulator pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# sum 1..10 = 55
val result = sum_to(10, 0)
expect(result).to_equal(55)
```

</details>

#### base case returns directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = factorial_tr(1, 1)
expect(result).to_equal(1)
```

</details>

#### tailrec with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sum_to(0, 42)
expect(result).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/tailrec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- @tailrec annotation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
