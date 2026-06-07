# Skia Compose Filter Specification

> Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` — the multi-stage image-filter composer mirroring Skia's `SkImageFilters::Compose(outer, inner)`.

<!-- sdn-diagram:id=compose_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compose_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compose_filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compose_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Compose Filter Specification

Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` — the multi-stage image-filter composer mirroring Skia's `SkImageFilters::Compose(outer, inner)`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-COMPOSE |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/compose_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `compose_filter_new`, `compose_filter_new2`, and `apply_compose` —
the multi-stage image-filter composer mirroring Skia's
`SkImageFilters::Compose(outer, inner)`.

## Scenarios

### compose_filter

#### compose_filter: single Identity stage returns input unchanged

1. var stages = [FilterNode]
2. stages push
   - Expected: out.width equals `src.width`
   - Expected: out.height equals `src.height`
   - Expected: _bitmap_diff(src, out) equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_test_bitmap(8, 6)
var stages = [FilterNode]()
stages.push(filter_node_identity())
val compose = compose_filter_new(stages)
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: two Identity stages return input unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_test_bitmap(8, 6)
val compose = compose_filter_new2(filter_node_identity(), filter_node_identity())
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: Blur then Invert produces a visibly different output than either alone

1. var blur only stages = [FilterNode]
2. blur only stages push
3. var invert only stages = [FilterNode]
4. invert only stages push


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_test_bitmap(12, 8)
val blur_node = filter_node_blur(blur_filter_new(2.0, 2.0))
val invert_node = filter_node_color(color_filter_invert())

var blur_only_stages = [FilterNode]()
blur_only_stages.push(blur_node)
val blur_only_out = apply_compose(src, compose_filter_new(blur_only_stages))

var invert_only_stages = [FilterNode]()
invert_only_stages.push(invert_node)
val invert_only_out = apply_compose(src, compose_filter_new(invert_only_stages))

val composed = apply_compose(src, compose_filter_new2(blur_node, invert_node))

# Composed result must differ from each single-stage result.
expect(_bitmap_diff(composed, blur_only_out)).to_be_greater_than(0 as i64)
expect(_bitmap_diff(composed, invert_only_out)).to_be_greater_than(0 as i64)
# And it should differ from the original src too.
expect(_bitmap_diff(composed, src)).to_be_greater_than(0 as i64)
```

</details>

#### compose_filter: empty stages list returns input unchanged (or handles gracefully)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_test_bitmap(5, 5)
val empty_stages = [FilterNode]()
val compose = compose_filter_new(empty_stages)
val out = apply_compose(src, compose)
expect(out.width).to_equal(src.width)
expect(out.height).to_equal(src.height)
expect(_bitmap_diff(src, out)).to_equal(0 as i64)
```

</details>

#### compose_filter: order matters — apply_compose(src, [Blur, Invert]) differs from apply_compose(src, [Invert, Blur])

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_test_bitmap(12, 8)
val blur_node = filter_node_blur(blur_filter_new(2.5, 2.5))
val invert_node = filter_node_color(color_filter_invert())

val blur_then_invert = apply_compose(src, compose_filter_new2(blur_node, invert_node))
val invert_then_blur = apply_compose(src, compose_filter_new2(invert_node, blur_node))

# Blur and invert do not commute exactly because blur clamps then invert
# negates around 255; the orders must produce different bitmaps.
expect(_bitmap_diff(blur_then_invert, invert_then_blur)).to_be_greater_than(0 as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
