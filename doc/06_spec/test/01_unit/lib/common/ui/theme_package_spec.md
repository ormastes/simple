# Theme Package Specification

> <details>

<!-- sdn-diagram:id=theme_package_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=theme_package_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

theme_package_spec -> std
theme_package_spec -> nogc_sync_mut
theme_package_spec -> app
theme_package_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=theme_package_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Package Specification

## Scenarios

### Folder theme packages

#### uses aetheric_dark as the registry default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_theme_id()).to_equal("aetheric_dark")
```

</details>

#### keeps glass_obsidian_dark as a compatibility alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_theme_alias("glass_obsidian_dark")).to_equal("aetheric_dark")
```

</details>

#### resolves the Aetheric package metadata and source reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = load_theme_package("aetheric_dark")
expect(pkg.id).to_equal("aetheric_dark")
expect(pkg.family_id).to_equal("aetheric")
expect(pkg.source_reference).to_end_with("config/themes/raw/simple_os_dark_refined_alignment/code.html")
expect(pkg.theme_path).to_equal("config/themes/aetheric_dark/theme.sdn")
expect(pkg.family_path).to_equal("config/themes/families/aetheric/theme.sdn")
```

</details>

#### assembles family shape CSS, base CSS, widgets, and icon defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = resolved_theme_css("aetheric_dark")
expect(css).to_contain("--radius-md")
expect(css).to_contain("--ui-accent: #adc6ff")
expect(css).to_contain(".widget-panel")
expect(css).to_contain("--theme-icon-terminal")
expect(css).to_contain("--theme-icon-command-palette")
```

</details>

#### keeps per-widget CSS and tokens on the resolved package

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = load_theme_package("aetheric_dark")
expect(pkg.token_map.get("--ui-accent") ?? "").to_equal("#adc6ff")
expect(pkg.widget_css_by_name.get("panel") ?? "").to_contain(".widget-panel")
expect(pkg.ui_theme.name).to_equal("aetheric_dark")
```

</details>

#### resolves numeric colors for BrowserBackend from the package

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = theme_numeric_colors("aetheric_dark")
expect(colors.bg).to_equal(0xFF0E0E10)
expect(colors.accent).to_equal(0xFFADC6FF)
expect(theme_bg("aetheric_dark")).to_equal(colors.bg)
expect(theme_accent("aetheric_dark")).to_equal(colors.accent)
```

</details>

#### resolves compositor glass config from the same package colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = theme_numeric_colors("aetheric_dark")
val cfg = theme_glass_config("aetheric_dark")
expect(cfg.accent_color).to_equal(colors.accent & 0x00FFFFFF)
expect(cfg.bg_top).to_equal(colors.bg & 0x00FFFFFF)
expect(cfg.blur_radius).to_equal(30)
```

</details>

#### resolves all default icon roles with labels colors and sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val icons = theme_icon_defaults("aetheric_dark")
match icons.get("terminal"):
    case Some(icon):
        expect(icon.icon_id).to_equal("terminal")
        expect(icon.label).to_equal("Terminal")
        expect(icon.color_token).to_equal("var(--ui-success)")
        expect(icon.size_role).to_equal("app")
    case _:
        expect("missing terminal icon").to_equal("resolved terminal icon")
match icons.get("command_palette"):
    case Some(icon):
        expect(icon.icon_id).to_equal("command_palette")
        expect(icon.size_role).to_equal("action")
    case _:
        expect("missing command palette icon").to_equal("resolved command palette icon")
match icons.get("error"):
    case Some(icon):
        expect(icon.color_token).to_equal("var(--ui-error)")
        expect(icon.size_role).to_equal("status")
    case _:
        expect("missing error icon").to_equal("resolved error icon")
```

</details>

#### web CSS includes package tokens and local widget overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("aetheric_dark")
expect(css).to_contain("Folder theme package")
expect(css).to_contain("--app-background-image")
expect(css).to_contain("0 0 40px var(--glass-accent)")
```

</details>

#### Simple Web app windows consume the selected theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = simple_web_app_html_with_theme("aetheric_dark", "Terminal", "pwd")
expect(html).to_contain("--ui-accent: #adc6ff")
expect(html).to_contain("SimpleOS shell via Simple Web")
```

</details>

#### validates the checked-in theme package graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val issues = validate_default_theme_package()
expect(issues.len()).to_equal(0)
```

</details>

#### renders a PASS validation report

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = render_theme_validation_report(validate_default_theme_package())
expect(report).to_contain("STATUS: PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/theme_package_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Folder theme packages

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
