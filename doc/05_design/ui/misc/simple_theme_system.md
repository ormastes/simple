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
- Snapshot: immutable `ThemeRenderSnapshot` with canonical identity, composed
  CSS, semantic scalar values, and material/source hashes.
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
- `theme_package_render_snapshot(id)`

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

Hosted WM installs the default package snapshot through
`install_default_host_wm_theme` before its first frame. Generated SimpleOS
installs the generated snapshot through `install_generated_simpleos_wm_theme`
before its first frame. Engine2D WM and Web adapters consume snapshot
projections and themed Simple Web HTML.

Runtime switching remains fail-closed. Before implementing it, add a
persistent hosted theme session at process entry (before renderer-worker
dispatch), an injectable counting source-reader seam, and scalar/wire read APIs
shared by WM, GUI, and Web. Canonical package/snapshot wire text is landed; its
native aggregate ABI remains an explicit incremental gate. The store mutex
protects one wire value; consumers copy it under lock and
decode private render objects after unlock. A fresh store per install,
module-global lazy/eager locks, mutable package dictionaries in the published
state, and aggregate-return reads are invalid designs.

The source-reader seam is not yet admitted because a cache-owning wrapper and
strict-versus-legacy missing-core validation contract remain unresolved. See
[the source-capture hard stop](../../../08_tracking/bug/theme_package_source_capture_design_hard_stop_2026-07-27.md).

`GlassConfig`, `GlassPortConfig`, and numeric/text Glass tokens are retained
compatibility or standalone APIs; they are not the production authoring path
for a new hosted/SimpleOS theme. New packages use registry + family/package
folders, then `theme-sync compile-to-spl`; review the resulting source diff
because `theme-sync diff` compares SDN snapshots rather than package output.

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

The active WM glass change has additional material/provenance boundaries in
[the detail design](../../wm_glass_theme_host_simpleos.md),
[system-test plan](../../../03_plan/sys_test/wm_glass_theme_host_simpleos.md),
and [agent plan](../../../03_plan/agent_tasks/wm_glass_theme_host_simpleos.md).
