# Skia Region Specification

> Tests for SkRegion — YX-banded multi-rectangle integer region used for complex clips (mirrors Skia's SkRegion).

<!-- sdn-diagram:id=region_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=region_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

region_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=region_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Region Specification

Tests for SkRegion — YX-banded multi-rectangle integer region used for complex clips (mirrors Skia's SkRegion).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-REGION |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/region_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkRegion — YX-banded multi-rectangle integer region used for complex
clips (mirrors Skia's SkRegion).

## Scenarios

### SkRegion

#### sk_region_empty: is_empty returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = sk_region_empty()
expect(reg.is_empty()).to_equal(true)
```

</details>

#### sk_region_from_rect: is_rect returns true, bounds matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_irect(10, 20, 110, 220)
val reg = sk_region_from_rect(r)
expect(reg.is_rect()).to_equal(true)
val b = reg.bounds()
expect(b.left).to_equal(10)
expect(b.top).to_equal(20)
expect(b.right).to_equal(110)
expect(b.bottom).to_equal(220)
```

</details>

#### SkRegion.contains: point inside rect returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = sk_region_from_rect(sk_irect(0, 0, 100, 100))
expect(reg.contains(50, 50)).to_equal(true)
```

</details>

#### SkRegion.contains: point outside rect returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = sk_region_from_rect(sk_irect(0, 0, 100, 100))
expect(reg.contains(200, 50)).to_equal(false)
```

</details>

#### op_union: two disjoint rects produces region with both bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sk_region_from_rect(sk_irect(0, 0, 10, 10))
val b = sk_region_from_rect(sk_irect(100, 100, 120, 120))
val u = a.op_union(b)
expect(u.rects.len()).to_be_greater_than(1)
val bb = u.bounds()
expect(bb.left).to_equal(0)
expect(bb.top).to_equal(0)
expect(bb.right).to_equal(120)
expect(bb.bottom).to_equal(120)
```

</details>

#### op_intersect: two overlapping rects produces the overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sk_region_from_rect(sk_irect(0, 0, 100, 100))
val b = sk_region_from_rect(sk_irect(50, 50, 150, 150))
val x = a.op_intersect(b)
expect(x.is_rect()).to_equal(true)
val bb = x.bounds()
expect(bb.left).to_equal(50)
expect(bb.top).to_equal(50)
expect(bb.right).to_equal(100)
expect(bb.bottom).to_equal(100)
```

</details>

#### op_intersect: disjoint rects produces empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sk_region_from_rect(sk_irect(0, 0, 10, 10))
val b = sk_region_from_rect(sk_irect(100, 100, 120, 120))
val x = a.op_intersect(b)
expect(x.is_empty()).to_equal(true)
```

</details>

#### op_difference: rect minus contained rect produces residual frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = sk_region_from_rect(sk_irect(0, 0, 100, 100))
val inner = sk_region_from_rect(sk_irect(25, 25, 75, 75))
val d = outer.op_difference(inner)
expect(d.is_empty()).to_equal(false)
expect(d.rects.len()).to_equal(4)
expect(d.contains(50, 50)).to_equal(false)
expect(d.contains(10, 10)).to_equal(true)
val bb = d.bounds()
expect(bb.left).to_equal(0)
expect(bb.top).to_equal(0)
expect(bb.right).to_equal(100)
expect(bb.bottom).to_equal(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
