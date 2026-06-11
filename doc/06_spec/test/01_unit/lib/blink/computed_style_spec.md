# Blink ComputedStyle Specification

> Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag for a DOM element after style cascade. Covers default values, visibility, positioning, margin totals, and block-level classification.

<!-- sdn-diagram:id=computed_style_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=computed_style_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

computed_style_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=computed_style_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink ComputedStyle Specification

Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag for a DOM element after style cascade. Covers default values, visibility, positioning, margin totals, and block-level classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/computed_style_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag
for a DOM element after style cascade. Covers default values, visibility,
positioning, margin totals, and block-level classification.

## Scenarios

### computed_style_default

#### display is Inline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
val is_inline = style.display == Display.Inline
expect(is_inline).to_equal(true)
```

</details>

#### is_visible returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
expect(style.is_visible()).to_equal(true)
```

</details>

#### is_positioned returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
expect(style.is_positioned()).to_equal(false)
```

</details>

### is_visible

#### opacity 0 returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
style.opacity = 0.0
expect(style.is_visible()).to_equal(false)
```

</details>

### is_block_level

#### Block display returns true, Inline returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
style.display = Display.Block
expect(style.is_block_level()).to_equal(true)
style.display = Display.Inline
expect(style.is_block_level()).to_equal(false)
```

</details>

### total_margin_horizontal

#### sum of left + right margin

1. style margin left = Length
2. style margin right = Length
   - Expected: style.total_margin_horizontal() equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
style.margin_left = Length(value: 12.0, unit: "px")
style.margin_right = Length(value: 8.0, unit: "px")
expect(style.total_margin_horizontal()).to_equal(20.0)
expect(style.total_margin_horizontal()).to_be_greater_than(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
