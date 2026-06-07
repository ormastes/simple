# Picture Layer Impl Specification

> <details>

<!-- sdn-diagram:id=picture_layer_impl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=picture_layer_impl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

picture_layer_impl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=picture_layer_impl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Picture Layer Impl Specification

## Scenarios

### PictureLayerImpl

#### from_layer wires base id

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = SkRect(left: 0.0, top: 0.0, right: 256.0, bottom: 256.0)
val base = Layer.root(bounds)
val layer = Layer(
    id: 7,
    parent_id: base.parent_id,
    kind: base.kind,
    bounds: base.bounds,
    transform_id: base.transform_id,
    clip_id: base.clip_id,
    effect_id: base.effect_id,
    scroll_id: base.scroll_id,
    contents_opaque: base.contents_opaque,
    is_drawable: base.is_drawable,
    needs_display: base.needs_display
)
val pic = SkPicture(cull_rect: bounds, op_count: 0, ops: [SkPictureOp]())
val rs = RasterSource.from_picture(pic)
val impl = PictureLayerImpl.from_layer(layer, rs)
expect(impl.base.id).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/picture_layer_impl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PictureLayerImpl

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
