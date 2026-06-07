# Paint Artifact Specification

> <details>

<!-- sdn-diagram:id=paint_artifact_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_artifact_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_artifact_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_artifact_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Artifact Specification

## Scenarios

### PaintArtifact

#### empty artifact has zero chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = PaintArtifact.empty()
expect(artifact.chunk_count()).to_equal(0)
```

</details>

#### empty artifact has zero items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = PaintArtifact.empty()
expect(artifact.item_count()).to_equal(0)
```

</details>

### PaintChunkProperties

#### root properties have all ids 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = PaintChunkProperties.root()
expect(props.transform_id).to_equal(0)
expect(props.clip_id).to_equal(0)
expect(props.effect_id).to_equal(0)
```

</details>

### PaintChunk

#### create stores begin and end indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = PaintChunkProperties.root()
val chunk = PaintChunk.create(begin_index: 0, end_index: 3, properties: props)
expect(chunk.begin_index).to_equal(0)
expect(chunk.end_index).to_equal(3)
```

</details>

#### create stores property triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = PaintChunkProperties(transform_id: 1, clip_id: 2, effect_id: 3)
val chunk = PaintChunk.create(begin_index: 0, end_index: 1, properties: props)
expect(chunk.properties.transform_id).to_equal(1)
expect(chunk.properties.clip_id).to_equal(2)
expect(chunk.properties.effect_id).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/blink/paint_artifact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PaintArtifact
- PaintChunkProperties
- PaintChunk

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
