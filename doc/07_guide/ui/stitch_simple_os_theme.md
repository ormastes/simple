# SimpleOS Theme Operator Guide

This is the production authority for SimpleOS, hosted WM, GUI, and Web WM
theme work. The canonical default is `aetheric_dark`, not an Obsidian or Glass
runtime preset.

## Production authority

`config/themes/theme.sdn` selects `default_theme: aetheric_dark`. It maps a
theme to its family and package folders, and its compatibility aliases resolve
legacy `obsidian_dark` and `glass_*` names to `aetheric_dark`. New production
code and configuration should use the canonical ID.

The package owner, `nogc_sync_mut.ui.theme_package`, resolves the registry,
family shape/widget CSS, concrete base/widget CSS, and family icons. It creates
an immutable `ThemeRenderSnapshot`; adapters consume that snapshot or its
scalar/CSS projections. They must not parse package files or duplicate palette
values on a render path.

```text
config/themes/theme.sdn (default: aetheric_dark)
  -> family + concrete package folders
  -> nogc_sync_mut.ui.theme_package
  -> immutable ThemeRenderSnapshot
  -> hosted / SimpleOS / GUI / Web adapter projections
```

Hosted startup calls `install_default_host_wm_theme` before the first frame.
The generated SimpleOS desktop calls
`install_generated_simpleos_wm_theme` before its first frame. These are the
canonical installation boundaries; neither a compositor constructor default nor
a key toggle is the production authority.

## Create or change a theme

1. Register the canonical theme and family in `config/themes/theme.sdn`.
2. Add or update the family package: shape CSS, widget defaults, and icon
   definitions.
3. Add or update the concrete package: manifest, base CSS, and widget CSS.
4. Regenerate the bare-metal snapshot with
   `bin/simple theme-sync compile-to-spl --theme=<registered-theme-id>
   --out=<path.spl>`, then inspect the source diff against the registered
   package. `theme-sync diff` compares SDN snapshots; it is not a package-to-
   generated-Simple drift checker.
5. Use the active WM glass design and system-test plan to supply the required
   source, semantic, and rendering evidence. A documentation change is not a
   runtime PASS claim.

Package CSS is the visual authority. Renderer adapters supply only structural
layout, reset, DOM, interaction rules, and package-variable references. The Web
source repair is independently accepted; live parser/render/pixel/event proof
remains **RUNTIME UNVERIFIED** under the
[dated handoff](../../08_tracking/bug/web_css_package_authority_adapter_2026-07-27.md).

## Compatibility and historical APIs

`glass/numeric_tokens.spl`, `glass/tokens.spl`, `GlassConfig`,
`GlassPortConfig`, and the Obsidian/Stitch presets remain supported for
compatibility or standalone legacy use. They are not the canonical
hosted/SimpleOS production source of truth, and the paired numeric/text token
files are not a required authoring workflow for a new package theme.

Historical examples that refer to `glass_obsidian_dark`, Obsidian as a runtime
default, editing two token files, or the `T` key as theme switching are kept as
legacy behavior only. Aliases preserve old callers; they do not establish a
second default or a second installation path.

## Troubleshooting

- Resolve the requested ID through `theme.sdn` first. An old Glass/Obsidian ID
  should resolve to `aetheric_dark` through the alias table.
- For a visual mismatch, inspect the package manifest, base/widget CSS, family
  shape/icons, generated snapshot identity, and the regeneration source diff
  in that order. Do not repair a package theme by editing legacy token twins
  or a `GlassConfig` preset.
- For a first-frame mismatch, verify the appropriate startup installer:
  `install_default_host_wm_theme` for hosted WM or
  `install_generated_simpleos_wm_theme` for generated SimpleOS.

## Current design and evidence work

- [WM glass architecture/detail design](../../05_design/wm_glass_theme_host_simpleos.md)
- [WM glass system-test plan](../../03_plan/sys_test/wm_glass_theme_host_simpleos.md)
- [WM glass agent plan](../../03_plan/agent_tasks/wm_glass_theme_host_simpleos.md)
- [Theme-system architecture](../../04_architecture/ui/simple_theme_system.md)
- [Theme-system detail design](../../05_design/ui/misc/simple_theme_system.md)

The WM glass documents describe active implementation and evidence boundaries.
Read their explicit status language before treating a design or generated
artifact as runtime verification.
