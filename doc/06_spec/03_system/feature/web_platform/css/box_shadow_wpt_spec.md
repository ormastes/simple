# Box Shadow Wpt Specification

> <details>

<!-- sdn-diagram:id=box_shadow_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=box_shadow_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

box_shadow_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=box_shadow_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Box Shadow Wpt Specification

## Scenarios

### WPT-derived box-shadow fallback rendering

#### renders single-layer offset box shadow behind the block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 4px 3px 0 #16a34a; }", "<div></div>")
expect(_pixel_at(pixels, 10, 4)).to_equal(0xFF16A34Au32)
expect(_pixel_at(pixels, 2, 2)).to_equal(0xFFFFFFFFu32)
```

</details>

#### renders blur-radius shadow coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 2px #dc2626; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFFDC2626u32)
```

</details>

#### parses blur and spread lengths before the shadow color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px #2563eb; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF2563EBu32)
```

</details>

#### keeps functional rgb shadow colors intact while tokenizing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rgb(37, 99, 235); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF2563EBu32)
```

</details>

#### composites functional rgba shadow colors over the white page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rgba(37, 99, 235, 0.5); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF92B1F5u32)
```

</details>

#### resolves named shadow colors through the shared color table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rebeccapurple; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF663399u32)
```

</details>

#### keeps functional hsl shadow colors intact while tokenizing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px hsl(120, 100%, 50%); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF00FF00u32)
```

</details>

#### resolves currentColor shadow colors from the element style

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; color: #db2777; box-shadow: 0px 0px 0px 2px currentColor; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFFDB2777u32)
```

</details>

#### renders comma-separated non-inset box shadow layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 4px 0px 0px #dc2626, 0px 4px 0px #2563eb; }", "<div></div>")
expect(_pixel_at(pixels, 10, 1)).to_equal(0xFFDC2626u32)
expect(_pixel_at(pixels, 1, 8)).to_equal(0xFF2563EBu32)
```

</details>

#### renders simple inset box shadows before text painting

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: inset 0px 0px 0px 2px #16a34a; }", "<div></div>")
expect(_pixel_at(pixels, 1, 0)).to_equal(0xFF16A34Au32)
expect(_pixel_at(pixels, 4, 3)).to_equal(0xFFFFFFFFu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived box-shadow fallback rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
