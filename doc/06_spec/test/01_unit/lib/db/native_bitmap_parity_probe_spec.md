# Native Bitmap Parity Probe Specification

> <details>

<!-- sdn-diagram:id=native_bitmap_parity_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_bitmap_parity_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_bitmap_parity_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_bitmap_parity_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Bitmap Parity Probe Specification

## Scenarios

### native bitmap parity probe

#### counts intersection bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = build_lhs_bitmap()
val rhs = build_rhs_bitmap()
val both = lhs.and_with(rhs)
val either = lhs.or_with(rhs)

expect(both.count()).to_equal(4)
expect(either.count()).to_equal(7)
```

</details>

#### reads intersection bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(0)).to_equal(true)
```

</details>

#### reads intersection bit 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(31)).to_equal(false)
```

</details>

#### reads intersection bit 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(32)).to_equal(true)
```

</details>

#### reads intersection bit 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(62)).to_equal(false)
```

</details>

#### reads intersection bit 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(63)).to_equal(true)
```

</details>

#### reads intersection bit 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(64)).to_equal(true)
```

</details>

#### reads intersection bit 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(95)).to_equal(false)
```

</details>

#### reads union bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(0)).to_equal(true)
```

</details>

#### reads union bit 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(31)).to_equal(true)
```

</details>

#### reads union bit 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(32)).to_equal(true)
```

</details>

#### reads union bit 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(62)).to_equal(true)
```

</details>

#### reads union bit 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(63)).to_equal(true)
```

</details>

#### reads union bit 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(64)).to_equal(true)
```

</details>

#### reads union bit 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(95)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native bitmap parity probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
