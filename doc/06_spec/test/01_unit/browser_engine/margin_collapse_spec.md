# Margin Collapse Specification

> <details>

<!-- sdn-diagram:id=margin_collapse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=margin_collapse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

margin_collapse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=margin_collapse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Margin Collapse Specification

## Scenarios

### collapse_margins_signed positive-positive

#### AC-3: collapses two positive margins to the larger value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collapse_margins_signed(20, 10)
expect(result).to_equal(20)
```

</details>

#### AC-3: collapses equal positive margins to same value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collapse_margins_signed(15, 15)
expect(result).to_equal(15)
```

</details>

#### AC-3: collapses zero and positive to positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collapse_margins_signed(0, 30)
expect(result).to_equal(30)
```

</details>

### collapse_margins_signed negative-positive mixed

#### AC-3: mixed margins: max(positives) + min(negatives)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# max(10) + min(-5) = 10 + (-5) = 5
val result = collapse_margins_signed(10, -5)
expect(result).to_equal(5)
```

</details>

#### AC-3: large negative with small positive gives negative result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# max(2) + min(-20) = 2 + (-20) = -18
val result = collapse_margins_signed(2, -20)
expect(result).to_equal(-18)
```

</details>

#### AC-3: two negatives produce the most-negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# max(negatives only) = 0; min(-8, -12) = -12 → result = -12
val result = collapse_margins_signed(-8, -12)
expect(result).to_equal(-12)
```

</details>

### collapse_margins_signed parent-child collapse

#### AC-3: parent-child top margin collapses when no border/padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulated: parent margin-top=10, child margin-top=20 → 20
val result = collapse_margins_signed(10, 20)
expect(result).to_equal(20)
```

</details>

#### AC-3: parent-child bottom margin collapses symmetrically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collapse_margins_signed(16, 8)
expect(result).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/margin_collapse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- collapse_margins_signed positive-positive
- collapse_margins_signed negative-positive mixed
- collapse_margins_signed parent-child collapse

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
