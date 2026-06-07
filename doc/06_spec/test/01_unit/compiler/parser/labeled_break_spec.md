# Labeled Break Specification

> <details>

<!-- sdn-diagram:id=labeled_break_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=labeled_break_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

labeled_break_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=labeled_break_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Labeled Break Specification

## Scenarios

### labeled break and continue

<details>
<summary>Advanced: basic labeled break exits outer loop (via fn return)</summary>

#### basic labeled break exits outer loop (via fn return)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = search_nested(2, 3)
expect(found).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: outer loop count via early return</summary>

#### outer loop count via early return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_count = count_outer(2)
expect(outer_count).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: inner break only exits inner loop</summary>

#### inner break only exits inner loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var outer_count = 0
for i in 0..3:
    for j in 0..5:
        j + 0
    outer_count = outer_count + 1
expect(outer_count).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: labeled while loop break via function</summary>

#### labeled while loop break via function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_while_limited(5)
expect(count).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: nested loops complete all iterations</summary>

#### nested loops complete all iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in 0..3:
    for j in 0..3:
        total = total + 1
expect(total).to_equal(9)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/labeled_break_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- labeled break and continue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
