# Blend Specification

> <details>

<!-- sdn-diagram:id=blend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blend Specification

## Scenarios

### Porter-Duff: blend_clear

#### returns all-zero regardless of inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_clear(_white(), _red())
expect r.r to_equal 0.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 0.0
```

</details>

### Porter-Duff: blend_src

#### returns src unchanged, ignores dst

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_src(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 1.0
```

</details>

### Porter-Duff: blend_dst

#### returns dst unchanged, ignores src

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_dst(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 1.0
expect r.b to_equal 1.0
expect r.a to_equal 1.0
```

</details>

### Porter-Duff: blend_src_over

#### with fully opaque src returns src

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_src_over(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 1.0
```

</details>

#### with fully transparent src returns dst

1. expect  approx
2. expect  approx
3. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transparent = SkColor4f(r: 0.5, g: 0.3, b: 0.1, a: 0.0)
val dst = _red()
val r = blend_src_over(transparent, dst)
expect _approx(r.r, 1.0) to_equal true
expect _approx(r.g, 0.0) to_equal true
expect _approx(r.a, 1.0) to_equal true
```

</details>

#### with half-alpha blends proportionally

1. expect  approx
2. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SkColor4f(r: 0.0, g: 0.0, b: 1.0, a: 0.5)
val dst = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val r = blend_src_over(src, dst)
expect _approx(r.b, 0.5) to_equal true
expect _approx(r.r, 0.5) to_equal true
```

</details>

### Porter-Duff: blend_plus

#### caps summed channels at 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_plus(_white(), _white())
expect r.r to_equal 1.0
expect r.a to_equal 1.0
```

</details>

#### adds channels below 1.0

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SkColor4f(r: 0.3, g: 0.3, b: 0.3, a: 0.3)
val b = SkColor4f(r: 0.4, g: 0.4, b: 0.4, a: 0.4)
val r = blend_plus(a, b)
expect _approx(r.r, 0.7) to_equal true
```

</details>

### Porter-Duff: blend_modulate

#### multiplies channels per-component

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val r = blend_modulate(a, b)
expect _approx(r.r, 0.25) to_equal true
```

</details>

### Porter-Duff: blend_screen

#### with black src returns dst

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = blend_screen(_black(), _red())
expect _approx(r.r, 1.0) to_equal true
```

</details>

#### screen formula: s + d - s*d

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val r = blend_screen(a, b)
# 0.5 + 0.5 - 0.25 = 0.75
expect _approx(r.r, 0.75) to_equal true
```

</details>

### Compose dispatcher

#### SrcOver routes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compose(_red(), _white(), SkBlendMode.SrcOver)
expect r.r to_equal 1.0
expect r.g to_equal 0.0
```

</details>

#### Clear routes to all-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compose(_white(), _white(), SkBlendMode.Clear)
expect r.r to_equal 0.0
expect r.a to_equal 0.0
```

</details>

#### Multiply routes to multiply mode

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val direct = blend_multiply(a, b)
val via_compose = compose(a, b, SkBlendMode.Multiply)
expect _approx(direct.r, via_compose.r) to_equal true
```

</details>

#### Screen routes to screen mode

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compose(_black(), _red(), SkBlendMode.Screen)
expect _approx(r.r, 1.0) to_equal true
```

</details>

#### Src routes to src

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compose(_red(), _white(), SkBlendMode.Src)
expect r.r to_equal 1.0
expect r.g to_equal 0.0
```

</details>

#### Dst routes to dst

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compose(_red(), _white(), SkBlendMode.Dst)
expect r.g to_equal 1.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/blend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Porter-Duff: blend_clear
- Porter-Duff: blend_src
- Porter-Duff: blend_dst
- Porter-Duff: blend_src_over
- Porter-Duff: blend_plus
- Porter-Duff: blend_modulate
- Porter-Duff: blend_screen
- Compose dispatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
