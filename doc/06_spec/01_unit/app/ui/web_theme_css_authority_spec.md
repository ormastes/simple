# Web Theme Css Authority Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Theme Css Authority Specification

## Scenarios

### Simple Web theme CSS authority

#### resolves a compatibility alias to the content-addressed package CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = load_theme_package("aetheric_dark")
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain("Folder theme package")
expect(css).to_contain("theme=aetheric_dark")
expect(css).to_contain("fingerprint={pkg.fingerprint}")
expect(css).to_contain("--ui-accent: #adc6ff")
expect(css).to_contain("--app-background-image")
```

</details>

#### preserves package-owned widget overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain(".widget-panel.focused, .wm-window.focused")
expect(css).to_contain("0 0 40px var(--glass-accent)")
```

</details>

#### does not select the legacy glass CSS generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/ui.web/html.spl")
expect(source.contains("generate_" + "glass_css")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_theme_css_authority_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web theme CSS authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
