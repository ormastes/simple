# Glass CSS Output Specification

> AC-2: Theme system supports HTML+CSS output (Electron-like) from glass design tokens.

<!-- sdn-diagram:id=glass_css_output_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_css_output_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_css_output_spec -> std
glass_css_output_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_css_output_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass CSS Output Specification

AC-2: Theme system supports HTML+CSS output (Electron-like) from glass design tokens.

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
| Source | `test/01_unit/lib/common/glass_css_output_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-2: Theme system supports HTML+CSS output (Electron-like) from glass
design tokens.

Verifies that:
- glass_tokens_to_css() emits all existing custom properties
- glass_tokens_to_css() emits new MD3 surface container custom properties
- glass_tokens_to_css() emits --glass-on-surface-variant
- generate_glass_css() produces a complete CSS string with :root block
- generate_glass_css() returns empty string for unknown themes
- Component CSS classes are present (widget-panel, glass-window, etc.)

## Key Concepts

| Concept | Description |
|---------|-------------|
| glass_tokens_to_css | Emits CSS custom properties from GlassDesignTokens |
| generate_glass_css | Full CSS entry point: :root vars + component styles |
| MD3 containers | --glass-surface-container-lowest through --glass-surface-container-highest |

## Scenarios

### glass_tokens_to_css existing properties

#### emits --glass-surface-primary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-primary:")
```

</details>

#### emits --glass-text-primary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-text-primary:")
```

</details>

#### emits --glass-accent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-accent:")
```

</details>

#### emits --glass-error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-error:")
```

</details>

#### emits --glass-blur-surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-blur-surface:")
```

</details>

#### emits --glass-radius-md

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-radius-md:")
```

</details>

#### emits --glass-shadow-md

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-shadow-md:")
```

</details>

#### emits --glass-spacing-md

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-spacing-md:")
```

</details>

#### emits --glass-duration-fast

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-duration-fast:")
```

</details>

### glass_tokens_to_css MD3 container properties

#### emits --glass-surface-container-lowest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-lowest:")
```

</details>

#### emits --glass-surface-container-low

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-low:")
```

</details>

#### emits --glass-surface-container:

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container:")
```

</details>

#### emits --glass-surface-container-high

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-high:")
```

</details>

#### emits --glass-surface-container-highest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-surface-container-highest:")
```

</details>

#### emits --glass-on-surface-variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("--glass-on-surface-variant:")
```

</details>

### glass_tokens_to_css Obsidian theme values

#### contains Obsidian text color #E3E0F3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("#E3E0F3")
```

</details>

#### contains Obsidian accent color #C6C6C8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("#C6C6C8")
```

</details>

#### contains Obsidian surface rgba with 18,18,31

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = GlassDesignTokens.obsidian_dark()
val css = glass_tokens_to_css(tokens, StitchMetadata.glass())
expect(css).to_contain("18,18,31")
```

</details>

### generate_glass_css full output

#### wraps tokens in :root block for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(":root")
```

</details>

#### includes component CSS for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".widget-panel")
```

</details>

#### includes glass-window CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-window")
```

</details>

#### includes glass-dock CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-dock")
```

</details>

#### includes glass-titlebar CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-titlebar")
```

</details>

#### includes glass-systembar CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_dark")
expect(css).to_contain(".glass-systembar")
```

</details>

#### returns empty for unknown theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("nonexistent_theme")
expect(css).to_equal("")
```

</details>

#### produces non-empty output for glass_light

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_light")
expect(css).to_contain(":root")
```

</details>

#### produces non-empty output for glass_obsidian_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain(":root")
```

</details>

#### obsidian CSS contains MD3 container variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain("--glass-surface-container-lowest")
```

</details>

#### obsidian CSS contains backdrop-filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_glass_css("glass_obsidian_dark")
expect(css).to_contain("backdrop-filter")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/stitch_design_system.md](doc/05_design/stitch_design_system.md)


</details>
