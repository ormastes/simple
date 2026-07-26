# Web Theme Css Authority Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
val fingerprint = theme_package_fingerprint("aetheric_dark")
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain("Folder theme package")
expect(css).to_contain("theme=aetheric_dark")
expect(css).to_contain("fingerprint={fingerprint}")
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
val source = file_read(HTML_SOURCE) + file_read(HTML_CSS_SOURCE)
expect(source.contains("generate_" + "glass_css")).to_equal(false)
```

</details>

#### accepts installed CSS only when its package fingerprint matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(HTML_SOURCE) + file_read(HTML_CSS_SOURCE)
expect(source).to_contain("active_theme_source_fingerprint")
expect(source).to_contain("resolved_theme_fingerprint")
expect(source).to_contain("installed_fingerprint == resolved_fingerprint")
expect(source).to_contain("resolved_theme_css")
expect(source.contains("load_theme_package(")).to_equal(false)
```

</details>

#### projects the selected package snapshot without carrying its aggregate into the browser frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(BROWSER_BACKEND_SOURCE)
expect(source).to_contain("theme_package_render_snapshot(state.tree.theme_name())")
expect(source.contains("load_theme_package(")).to_equal(false)
```

</details>

#### replaces only root attributes owned by the theme envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/ui.web/wm.js")
expect(source).to_contain("_applyThemeRootAttrs(rootAttrs)")
expect(source).to_contain("root.removeAttribute(attrName)")
expect(source).to_contain("Object.prototype.hasOwnProperty.call(entry, 'root_attrs')")
expect(source).to_contain("if (hasRootAttrs) envelope.root_attrs = root_attrs")
expect(source.contains("startsWith('data-wm-')")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_theme_css_authority_spec.spl` |
| Updated | 2026-07-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web theme CSS authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
