# Glass Token Unification Specification

> AC-1: GUI lib and window manager consume the same theme tokens -- a single theme change propagates to both.

<!-- sdn-diagram:id=glass_token_unification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_token_unification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_token_unification_spec -> std
glass_token_unification_spec -> os
glass_token_unification_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_token_unification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Token Unification Specification

AC-1: GUI lib and window manager consume the same theme tokens -- a single theme change propagates to both.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/01_unit/lib/common/glass_token_unification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-1: GUI lib and window manager consume the same theme tokens -- a single
theme change propagates to both.

AC-7: Bugs in existing GUI/WM/theme code identified and fixed. The primary
bug is that glass_effects.spl hardcodes values instead of importing from
glass_numeric_tokens.spl.

After the fix, GlassConfig factory methods in glass_effects.spl must import
from glass_numeric_tokens.spl constants, so both the compositor (baremetal
u64 values) and the GUI widget lib (CSS rgba strings in glass_tokens.spl)
derive from the same single source of truth.

## Key Concepts

| Concept | Description |
|---------|-------------|
| GlassConfig | Compositor-level struct with u64 color/blur/shadow fields |
| GlassColorTokens | CSS-text token struct for the widget system |
| glass_numeric_tokens | Canonical u64 hex constants (single source of truth) |

## Behavior

- GlassConfig.dark().surface_color must equal GLASS_DARK_SURFACE
- GlassConfig.dark().surface_alpha must equal GLASS_DARK_SURFACE_A
- GlassConfig.dark().border_color must equal GLASS_DARK_BORDER
- GlassConfig.dark().border_alpha must equal GLASS_DARK_BORDER_A
- GlassConfig.dark().accent_color must equal GLASS_DARK_ACCENT
- GlassConfig.dark().blur_radius must equal GLASS_BLUR_SURFACE
- GlassConfig.dark().shadow_blur must equal GLASS_SHADOW_BLUR
- GlassConfig.dark().shadow_offset must equal GLASS_SHADOW_OFFSET
- GlassConfig.light().surface_color must equal GLASS_LIGHT_SURFACE
- GlassConfig.light().border_alpha must equal GLASS_LIGHT_BORDER_A
- GlassConfig.obsidian_dark().surface_color must equal GLASS_OBSIDIAN_SURFACE
- GlassConfig.obsidian_dark().accent_color must equal GLASS_OBSIDIAN_ACCENT

## Scenarios

### GlassConfig.dark() token unification

#### surface_color matches GLASS_DARK_SURFACE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.surface_color).to_equal(GLASS_DARK_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_DARK_SURFACE_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.surface_alpha).to_equal(GLASS_DARK_SURFACE_A.to_u8())
```

</details>

#### blur_radius matches GLASS_BLUR_SURFACE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
```

</details>

#### border_color matches GLASS_DARK_BORDER

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.border_color).to_equal(GLASS_DARK_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_DARK_BORDER_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.border_alpha).to_equal(GLASS_DARK_BORDER_A.to_u8())
```

</details>

#### shadow_offset matches GLASS_SHADOW_OFFSET

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
```

</details>

#### shadow_blur matches GLASS_SHADOW_BLUR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
```

</details>

#### shadow_alpha matches GLASS_DARK_SHADOW_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.shadow_alpha).to_equal(GLASS_DARK_SHADOW_A.to_u8())
```

</details>

#### accent_color matches GLASS_DARK_ACCENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.accent_color).to_equal(GLASS_DARK_ACCENT.to_u32())
```

</details>

#### accent2_color matches GLASS_DARK_ACCENT2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.accent2_color).to_equal(GLASS_DARK_ACCENT2.to_u32())
```

</details>

#### bg_top matches GLASS_DARK_BG_TOP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.bg_top).to_equal(GLASS_DARK_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_DARK_BG_BOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.dark()
expect(config.bg_bottom).to_equal(GLASS_DARK_BG_BOT.to_u32())
```

</details>

### GlassConfig.light() token unification

#### surface_color matches GLASS_LIGHT_SURFACE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.surface_color).to_equal(GLASS_LIGHT_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_LIGHT_SURFACE_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.surface_alpha).to_equal(GLASS_LIGHT_SURFACE_A.to_u8())
```

</details>

#### border_color matches GLASS_LIGHT_BORDER

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.border_color).to_equal(GLASS_LIGHT_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_LIGHT_BORDER_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.border_alpha).to_equal(GLASS_LIGHT_BORDER_A.to_u8())
```

</details>

#### accent_color matches GLASS_LIGHT_ACCENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.accent_color).to_equal(GLASS_LIGHT_ACCENT.to_u32())
```

</details>

#### accent2_color matches GLASS_LIGHT_ACCENT2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.accent2_color).to_equal(GLASS_LIGHT_ACCENT2.to_u32())
```

</details>

#### bg_top matches GLASS_LIGHT_BG_TOP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.bg_top).to_equal(GLASS_LIGHT_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_LIGHT_BG_BOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.light()
expect(config.bg_bottom).to_equal(GLASS_LIGHT_BG_BOT.to_u32())
```

</details>

### GlassConfig.obsidian_dark() token unification

#### surface_color matches GLASS_OBSIDIAN_SURFACE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.surface_color).to_equal(GLASS_OBSIDIAN_SURFACE.to_u32())
```

</details>

#### surface_alpha matches GLASS_OBSIDIAN_SURFACE_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.surface_alpha).to_equal(GLASS_OBSIDIAN_SURFACE_A.to_u8())
```

</details>

#### border_color matches GLASS_OBSIDIAN_BORDER

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.border_color).to_equal(GLASS_OBSIDIAN_BORDER.to_u32())
```

</details>

#### border_alpha matches GLASS_OBSIDIAN_BORDER_A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.border_alpha).to_equal(GLASS_OBSIDIAN_BORDER_A.to_u8())
```

</details>

#### accent_color matches GLASS_OBSIDIAN_ACCENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.accent_color).to_equal(GLASS_OBSIDIAN_ACCENT.to_u32())
```

</details>

#### bg_top matches GLASS_OBSIDIAN_BG_TOP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.bg_top).to_equal(GLASS_OBSIDIAN_BG_TOP.to_u32())
```

</details>

#### bg_bottom matches GLASS_OBSIDIAN_BG_BOT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GlassConfig.obsidian_dark()
expect(config.bg_bottom).to_equal(GLASS_OBSIDIAN_BG_BOT.to_u32())
```

</details>

### Shared constants across themes

#### all themes share the same blur_radius

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
expect(light.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
expect(obsidian.blur_radius).to_equal(GLASS_BLUR_SURFACE.to_u32())
```

</details>

#### all themes share the same shadow_blur

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
expect(light.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
expect(obsidian.shadow_blur).to_equal(GLASS_SHADOW_BLUR.to_u32())
```

</details>

#### all themes share the same shadow_offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark = GlassConfig.dark()
val light = GlassConfig.light()
val obsidian = GlassConfig.obsidian_dark()
expect(dark.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
expect(light.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
expect(obsidian.shadow_offset).to_equal(GLASS_SHADOW_OFFSET.to_i32())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/stitch_design_system.md](doc/05_design/stitch_design_system.md)


</details>
