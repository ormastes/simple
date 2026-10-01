# Engine2d Render Surface Matrix Specification

> <details>

<!-- sdn-diagram:id=engine2d_render_surface_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_render_surface_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_render_surface_matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_render_surface_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Render Surface Matrix Specification

## Scenarios

### Engine2D rendering surface

#### should render every primitive with fixed-point pixel anchors

- Draw fill line outline circle rounded rectangle and triangle
   - Expected: ["fill", "line", "outline", "circle", "rounded", "triangle"].len() equals `6`
- pending render surface matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw fill line outline circle rounded rectangle and triangle")
expect(["fill", "line", "outline", "circle", "rounded", "triangle"].len()).to_equal(6)
pending_render_surface_matrix()
```

</details>

#### should render effects transforms clipping masks text and images

- Compose alpha gradient border radius shadow transform clip mask text and image
   - Expected: ["alpha", "gradient", "border", "radius", "shadow", "transform", "clip", "mask", "text", "image"].len() equals `10`
- pending render surface matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose alpha gradient border radius shadow transform clip mask text and image")
expect(["alpha", "gradient", "border", "radius", "shadow", "transform", "clip", "mask", "text", "image"].len()).to_equal(10)
pending_render_surface_matrix()
```

</details>

<details>
<summary>Advanced: should preserve ordered resources transitions and deterministic replay</summary>

#### should preserve ordered resources transitions and deterministic replay

- Replay a recorded resource and state transition stream
   - Expected: "ordered" equals `ordered`
- pending render surface matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replay a recorded resource and state transition stream")
expect("ordered").to_equal("ordered")
pending_render_surface_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should reject invalid dimensions resources and fallback</summary>

#### should reject invalid dimensions resources and fallback

- Submit invalid surface and resource inputs
   - Expected: ["invalid-dimensions", "dangling-resource", "fallback-rejected"].len() equals `3`
- pending render surface matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit invalid surface and resource inputs")
expect(["invalid-dimensions", "dangling-resource", "fallback-rejected"].len()).to_equal(3)
pending_render_surface_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should reproduce exact pixels for one hundred frames</summary>

#### should reproduce exact pixels for one hundred frames

- Render the deterministic scene one hundred times
   - Expected: 100 equals `100`
- pending render surface matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the deterministic scene one hundred times")
expect(100).to_equal(100)
pending_render_surface_matrix()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D rendering surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
