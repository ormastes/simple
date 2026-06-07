# Drawing Document Specification

> <details>

<!-- sdn-diagram:id=drawing_document_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=drawing_document_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

drawing_document_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=drawing_document_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Drawing Document Specification

## Scenarios

### DrawingDocument — new document

#### new document has 1 layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = DrawingDocument.new(800, 600)
expect(doc.layer_count()).to_equal(1)
```

</details>

#### default layer is named Background

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = DrawingDocument.new(800, 600)
val layer = doc.active_layer()
expect(layer.name).to_equal("Background")
```

</details>

### DrawingDocument — add and remove layers

#### add layer increases count

1. var doc = DrawingDocument new
2. doc add layer
   - Expected: doc.layer_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = DrawingDocument.new(800, 600)
val layer = DrawingLayer.new_raster("Layer 1", 800, 600)
doc.add_layer(layer)
expect(doc.layer_count()).to_equal(2)
```

</details>

#### remove layer decreases count

1. var doc = DrawingDocument new
2. doc add layer
3. doc remove layer
   - Expected: doc.layer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = DrawingDocument.new(800, 600)
val layer = DrawingLayer.new_raster("Layer 1", 800, 600)
doc.add_layer(layer)
doc.remove_layer(1)
expect(doc.layer_count()).to_equal(1)
```

</details>

#### active layer index is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = DrawingDocument.new(800, 600)
expect(doc.active_layer_index >= 0).to_equal(true)
expect(doc.active_layer_index < doc.layer_count()).to_equal(true)
```

</details>

### DrawingLayer — default properties

#### new raster layer is visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = DrawingLayer.new_raster("Test", 100, 100)
expect(layer.visible).to_equal(true)
```

</details>

#### new raster layer is not locked

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = DrawingLayer.new_raster("Test", 100, 100)
expect(layer.locked).to_equal(false)
```

</details>

#### new raster layer has opacity 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = DrawingLayer.new_raster("Test", 100, 100)
expect(layer.opacity > 0.99).to_equal(true)
expect(layer.opacity < 1.01).to_equal(true)
```

</details>

#### new raster layer has Normal blend mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = DrawingLayer.new_raster("Test", 100, 100)
expect(layer.blend_mode.to_text()).to_equal("Normal")
```

</details>

### BlendMode — to_text

#### Normal returns correct string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = BlendMode.Normal
expect(mode.to_text()).to_equal("Normal")
```

</details>

#### Multiply returns correct string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = BlendMode.Multiply
expect(mode.to_text()).to_equal("Multiply")
```

</details>

#### Screen returns correct string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = BlendMode.Screen
expect(mode.to_text()).to_equal("Screen")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/drawing_document_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DrawingDocument — new document
- DrawingDocument — add and remove layers
- DrawingLayer — default properties
- BlendMode — to_text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
