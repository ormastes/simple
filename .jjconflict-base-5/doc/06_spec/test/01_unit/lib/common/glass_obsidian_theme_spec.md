# Obsidian Dark Theme Specification

> AC-6: Latest Stitch "Obsidian" dark theme applied to glass_tokens.spl and glass_numeric_tokens.spl.

<!-- sdn-diagram:id=glass_obsidian_theme_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_obsidian_theme_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_obsidian_theme_spec -> std
glass_obsidian_theme_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_obsidian_theme_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Obsidian Dark Theme Specification

AC-6: Latest Stitch "Obsidian" dark theme applied to glass_tokens.spl and glass_numeric_tokens.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/01_unit/lib/common/glass_obsidian_theme_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-6: Latest Stitch "Obsidian" dark theme applied to glass_tokens.spl and
glass_numeric_tokens.spl.

Verifies that:
- GlassColorTokens.obsidian_dark() exists and returns correct MD3 color values
- GlassDesignTokens.obsidian_dark() composes the right sub-token structs
- Numeric token constants match the Stitch MD3 spec
- MD3 surface container tier fields (6 tiers) are present
- glass_theme.spl recognizes "glass_obsidian_dark" as a valid glass theme
- glass_design_tokens() dispatches correctly for the obsidian theme

## Key Concepts

| Concept | Description |
|---------|-------------|
| GlassColorTokens | CSS-text token struct, extended with MD3 container tiers |
| Obsidian dark | Stitch MD3 theme: surface=#12121f, text=#E3E0F3, accent=#C6C6C8 |
| Surface container tiers | MD3 defines 5 container levels (lowest through highest) |
| on_surface_variant | MD3 secondary text color (#CCC4CE for Obsidian) |

## Scenarios

### GlassColorTokens.obsidian_dark()

#### has surface_primary matching Obsidian surface #12121f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_primary).to_contain("18,18,31")
```

</details>

#### has text_primary matching MD3 on_surface #E3E0F3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.text_primary).to_equal("#E3E0F3")
```

</details>

#### has accent matching MD3 primary #C6C6C8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.accent).to_equal("#C6C6C8")
```

</details>

#### has error matching MD3 error #FFB4AB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.error).to_equal("#FFB4AB")
```

</details>

#### has text_secondary with reduced opacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.text_secondary).to_contain("0.6")
```

</details>

### GlassColorTokens.obsidian_dark() MD3 surface containers

#### has surface_container_lowest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_container_lowest).to_contain("13,13,26")
```

</details>

#### has surface_container_low

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_container_low).to_contain("26,26,40")
```

</details>

#### has surface_container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_container).to_contain("30,30,44")
```

</details>

#### has surface_container_high

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_container_high).to_contain("41,41,55")
```

</details>

#### has surface_container_highest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.surface_container_highest).to_contain("52,51,66")
```

</details>

#### has on_surface_variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.obsidian_dark()
expect(tokens.on_surface_variant).to_contain("204,196,206")
```

</details>

### Obsidian numeric token constants

#### GLASS_OBSIDIAN_SURFACE equals 0x0012121F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_SURFACE).to_equal(0x0012121F)
```

</details>

#### GLASS_OBSIDIAN_TEXT equals 0x00E3E0F3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_TEXT).to_equal(0x00E3E0F3)
```

</details>

#### GLASS_OBSIDIAN_ACCENT equals 0x00C6C6C8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_ACCENT).to_equal(0x00C6C6C8)
```

</details>

#### GLASS_OBSIDIAN_ERROR equals 0x00FFB4AB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_ERROR).to_equal(0x00FFB4AB)
```

</details>

#### GLASS_OBSIDIAN_RADIUS_MD equals 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_RADIUS_MD).to_equal(8)
```

</details>

#### GLASS_OBSIDIAN_CONTAINER_LOWEST equals 0x000D0D1A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_CONTAINER_LOWEST).to_equal(0x000D0D1A)
```

</details>

#### GLASS_OBSIDIAN_CONTAINER_LOW equals 0x001A1A28

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_CONTAINER_LOW).to_equal(0x001A1A28)
```

</details>

#### GLASS_OBSIDIAN_CONTAINER equals 0x001E1E2C

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_CONTAINER).to_equal(0x001E1E2C)
```

</details>

#### GLASS_OBSIDIAN_CONTAINER_HIGH equals 0x00292937

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_CONTAINER_HIGH).to_equal(0x00292937)
```

</details>

#### GLASS_OBSIDIAN_CONTAINER_HIGHEST equals 0x00343342

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLASS_OBSIDIAN_CONTAINER_HIGHEST).to_equal(0x00343342)
```

</details>

### GlassDesignTokens.obsidian_dark()

#### colors.text_primary matches Obsidian value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
expect(tokens.colors.text_primary).to_equal("#E3E0F3")
```

</details>

#### colors.accent matches Obsidian value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
expect(tokens.colors.accent).to_equal("#C6C6C8")
```

</details>

#### blur tokens are default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
expect(tokens.blur.surface_blur).to_equal(20)
expect(tokens.blur.elevated_blur).to_equal(40)
```

</details>

### glass_theme Obsidian recognition

#### is_glass_theme returns true for glass_obsidian_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_glass_theme("glass_obsidian_dark")).to_equal(true)
```

</details>

#### is_glass_theme still recognizes glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_glass_theme("glass_dark")).to_equal(true)
```

</details>

#### is_glass_theme still recognizes glass_light

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_glass_theme("glass_light")).to_equal(true)
```

</details>

#### is_glass_theme returns false for unknown theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_glass_theme("unknown_theme")).to_equal(false)
```

</details>

#### glass_design_tokens dispatches obsidian theme correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = glass_design_tokens("glass_obsidian_dark")
expect(tokens.colors.text_primary).to_equal("#E3E0F3")
```

</details>

#### glass_design_tokens still works for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = glass_design_tokens("glass_dark")
expect(tokens.colors.text_primary).to_equal("#F5F5F7")
```

</details>

### Existing themes with MD3 container fields

#### dark theme has surface_container_lowest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.dark()
expect(tokens.surface_container_lowest).to_contain("rgba")
```

</details>

#### dark theme has on_surface_variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.dark()
expect(tokens.on_surface_variant).to_contain("rgba")
```

</details>

#### light theme has surface_container_lowest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.light()
expect(tokens.surface_container_lowest).to_contain("rgba")
```

</details>

#### light theme has on_surface_variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassColorTokens.light()
expect(tokens.on_surface_variant).to_contain("rgba")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/stitch_design_system.md](doc/05_design/stitch_design_system.md)


</details>
