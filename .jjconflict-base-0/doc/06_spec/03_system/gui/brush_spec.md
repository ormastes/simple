# Brush Specification

> <details>

<!-- sdn-diagram:id=brush_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=brush_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

brush_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=brush_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Brush Specification

## Scenarios

### BrushConfig — default_brush

#### default brush size is greater than 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = BrushConfig.default_brush()
expect(b.size > 0.0).to_equal(true)
```

</details>

#### default brush opacity is greater than 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = BrushConfig.default_brush()
expect(b.opacity > 0.0).to_equal(true)
```

</details>

### BrushConfig — default_eraser

#### default eraser is a valid config with size greater than 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = BrushConfig.default_eraser()
expect(e.size > 0.0).to_equal(true)
```

</details>

#### default eraser opacity is greater than 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = BrushConfig.default_eraser()
expect(e.opacity > 0.0).to_equal(true)
```

</details>

### BrushConfig — effective_size with pressure

#### pressure 0.5 reduces size when pressure_size is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = BrushConfig.default_brush()
val eff = b.effective_size(0.5)
val half = b.size * 0.5
expect(eff > half - 0.01).to_equal(true)
expect(eff < half + 0.01).to_equal(true)
```

</details>

#### pressure has no effect when pressure_size is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = BrushConfig.pencil()
val eff = b.effective_size(0.5)
expect(eff > b.size - 0.01).to_equal(true)
expect(eff < b.size + 0.01).to_equal(true)
```

</details>

### BrushConfig — effective_opacity with pressure

#### pressure 0.5 reduces opacity when pressure_opacity is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = BrushConfig.default_eraser()
val eff = e.effective_opacity(0.5)
val half = e.opacity * 0.5
expect(eff > half - 0.01).to_equal(true)
expect(eff < half + 0.01).to_equal(true)
```

</details>

#### pressure has no effect when pressure_opacity is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = BrushConfig.default_brush()
val eff = b.effective_opacity(0.5)
expect(eff > b.opacity - 0.01).to_equal(true)
expect(eff < b.opacity + 0.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/brush_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrushConfig — default_brush
- BrushConfig — default_eraser
- BrushConfig — effective_size with pressure
- BrushConfig — effective_opacity with pressure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
