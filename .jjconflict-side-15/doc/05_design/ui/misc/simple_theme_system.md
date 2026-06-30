# Detail Design: Simple Theme System

## Registry Schema

`config/themes/theme.sdn`:

```sdn
default_theme: aetheric_dark
families:
    aetheric: config/themes/families/aetheric/theme.sdn
themes:
    aetheric_dark: config/themes/aetheric_dark/theme.sdn
aliases:
    glass_obsidian_dark: aetheric_dark
required_widgets:
    - panel
required_icons:
    - terminal
```

Family package:

```sdn
id: aetheric
display_name: Aetheric
shape_css: config/themes/families/aetheric/shape.css
icons: config/themes/families/aetheric/icons.sdn
widget_css_dir: config/themes/families/aetheric/widgets
```

Concrete theme package:

```sdn
id: aetheric_dark
display_name: Aetheric Dark
family: aetheric
base_css: config/themes/aetheric_dark/base.css
widget_css_dir: config/themes/aetheric_dark/widgets
source_raw_reference: config/themes/raw/simple_os_dark_refined_alignment/code.html
```

Icon package sections are `apps`, `system`, `navigation`, `content`, `status`, `labels`, `colors`, and `sizes`. Every `required_icons` role must resolve to an icon id, human label, semantic `var(--token)` color, and size role.

## ResolvedThemePackage

`ResolvedThemePackage` contains:

- Identity: `id`, `display_name`, `family_id`, `registry_path`, `theme_path`, `family_path`.
- CSS chunks: `shape_css`, `family_widget_css`, `base_css`, `theme_widget_css`, `icon_css`.
- Maps: `token_map`, `widget_css_by_name`, `icons`.
- Renderer values: numeric colors, `UITheme`, `GlassDesignTokens`, and `ResolvedThemeGlassConfig`.
- Cache data: `source_paths`, `fingerprint`, `mtime_key`.

Public helpers:

- `default_theme_id()`
- `resolve_theme_alias(id)`
- `load_theme_package(id)`
- `resolved_theme_css(id)`
- `theme_ui_theme(id)`
- `theme_design_tokens(id)`
- `theme_numeric_colors(id)`
- `theme_glass_config(id)`
- `theme_icon_defaults(id)`

## CSS Composition

`resolved_theme_css(id)` emits:

1. Family shape CSS.
2. Family widget defaults and family widget CSS.
3. Theme base CSS.
4. Theme widget overrides.
5. Icon custom properties.

Renderer-generated CSS may add layout, reset, DOM, and interaction rules, but package CSS remains the final visual source for colors, shape, glass surfaces, widget styling, and icon defaults.

## Shared GUI Backends

`generate_css(theme)` is the shared CSS path for Electron/Chromium and pure Simple Web. Electron app windows use `themed_simple_web_html_with_theme`, the same wrapper as Simple Web app-window rendering, avoiding duplicated inline palettes.

`BrowserBackend` resolves package colors and CSS at construction, stores them on the backend, and applies cached values to the DOM root during render.

Hosted WM uses `theme_glass_config` for compositor and boot splash glass settings. Engine2D WM uses `theme_numeric_colors` and themed Simple Web HTML for its browser demo content.

## Validation

`simple lint` calls `validate_default_theme_package()` for `config/themes/**`. Validation fails on:

- Missing registry, family, theme, shape, base, icon, or source files.
- Missing required widget CSS in theme/family/defaults.
- Missing required icon id, label, color, or size.
- Icon colors that do not use semantic `var(--token)` references.
- Undefined `var(--token)` references.
- Shape tokens in theme base CSS or theme tokens in family shape/widget CSS.
- Local widget CSS defining new tokens instead of consuming existing ones.

Invalid default themes must fail verify with exact file/key/path diagnostics.
