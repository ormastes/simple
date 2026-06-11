# Engine2d Color Specification

> <details>

<!-- sdn-diagram:id=engine2d_color_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_color_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_color_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_color_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Color Specification

## Scenarios

### Engine2D Color Utilities

#### rgb construction

#### rgb creates correct packed color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(255, 128, 64)
expect(color_r(c)).to_equal(255)
expect(color_g(c)).to_equal(128)
expect(color_b(c)).to_equal(64)
```

</details>

#### rgb sets full alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(0, 0, 0)
expect(color_a(c)).to_equal(255)
```

</details>

#### rgba construction

#### rgba includes alpha channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba(255, 0, 0, 128)
expect(color_r(c)).to_equal(255)
expect(color_a(c)).to_equal(128)
```

</details>

#### color extraction

#### extracts zero channels correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(0, 0, 0)
expect(color_r(c)).to_equal(0)
expect(color_g(c)).to_equal(0)
expect(color_b(c)).to_equal(0)
```

</details>

#### extracts max channels correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(255, 255, 255)
expect(color_r(c)).to_equal(255)
expect(color_g(c)).to_equal(255)
expect(color_b(c)).to_equal(255)
```

</details>

#### lerp_color

#### lerp at t=0 returns first color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = lerp_color(rgb(255, 0, 0), rgb(0, 0, 255), 0)
expect(color_r(c)).to_equal(255)
expect(color_b(c)).to_equal(0)
```

</details>

#### lerp at t=255 returns second color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = lerp_color(rgb(255, 0, 0), rgb(0, 0, 255), 255)
expect(color_r(c)).to_equal(0)
expect(color_b(c)).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/engine2d_color_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Color Utilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
