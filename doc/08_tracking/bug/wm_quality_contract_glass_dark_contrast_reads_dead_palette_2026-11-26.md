# BUG: WM theme quality contrast for glass_dark reads a palette the cascade overrides

Status: VERIFIED 2026-11-26 (owner decision: glass_dark uses its own palette).
Where: `src/app/ui.web/html.spl` `generate_css` (and its twin in
`src/app/ui.web/html_css.spl`), `src/app/ui.web/wm_quality_contract.spl`
`wm_theme_quality_report`, `config/themes/theme.sdn` aliases.
Spec: `test/01_unit/app/ui/web_wm_modern_shell_spec.spl`, example "reports
theme quality for color size layout motion and shell affordances":
`expected 998 to be greater than 1700` (band 1700..1900).

## Measured (release/1.0.0 79445b063c4, Linux aarch64, seed cargo-target-wr-seed1126b)

- `config/themes/theme.sdn` aliases `glass_dark: aetheric_dark`, and
  `generate_css` resolves the alias first, so its
  `if canonical_theme == "glass_dark":` palette branch (`bg = "#0A0A0F"`,
  `GlassColorTokens.dark()` text) is unreachable. `aetheric_dark` falls into
  the generic `is_dark` branch (`#1e1e2e` / `#cdd6f4`). At 091a8da3be8
  (2026-07-24) the branch tested the raw requested `theme`, so glass_dark
  still got the glass palette.
- `build_modern_theme_css("glass_dark")` (315582 bytes) has two `--ui-bg`
  declarations: `#1e1e2e` at offset 199 and the aetheric package's
  `#0e0e10` at offset 294007, which wins in the cascade.
- `wm_theme_quality_report` reads the FIRST `--ui-bg`, so it measures
  `#cdd6f4` on `#1e1e2e` (998), not the effective background.

## Owner questions

1. Is the glass palette (`#0A0A0F`, ~17-19:1) still canonical for a
   glass_dark request, or is aetheric_dark's package palette now the authority?
2. Should the quality contract measure the effective (last) declaration?

Then either restore the reachable palette branch (and delete whichever branch
is dead) or move the 1700..1900 band to the measured authority.

## Fix 2026-11-26 (owner decision: glass_dark uses its own palette)

1. `config/themes/theme.sdn` no longer aliases `glass_dark` to `aetheric_dark`,
   so `generate_css`'s glass_dark branch runs (`bg #0A0A0F`, text
   `GlassColorTokens.dark().text_primary` = `#F5F5F7`).
2. Dropping the alias alone left `glass_dark` an unregistered package id:
   `load_theme_package` returned an empty package (no family, 4715 B CSS),
   a regression for package consumers (browser backends, session draw IR,
   Simple Web window renderer). So `glass_dark` is now a real registered
   package, `config/themes/glass_dark/` (family aetheric for shape, icons and
   widgets; `base.css` is the aetheric_dark recipe with the palette replaced
   by `GlassColorTokens.dark`: bg/app-bg `#0A0A0F`, fg `#F5F5F7`, accent
   `#0A84FF`, surfaces `rgba(30,30,35,0.72)` / `rgba(44,44,50,0.88)`,
   borders `rgba(255,255,255,0.08/0.18)`, status colours).
3. The registry file is hashed into every package's source manifest, so the
   tracked `generated/aetheric_dark_theme_snapshot.spl` manifest sha was
   refreshed (a0b9ee05... -> 5872aed6...; material sha unchanged). The
   alias-only commit had already broken `theme_package_spec`'s bare-metal
   snapshot parity example; the earlier before/after set did not include that
   spec.

Evidence (Linux aarch64, seed cargo-target-wr-seed1126b):

- `theme_package_spec` 19/20 (baseline, glass example red) -> 20/20; the new
  example pins id/family/palette and `theme_bg`/`theme_accent` =
  `0xFF0A0A0F`/`0xFF0A84FF`.
- `wm_theme_quality_report("glass_dark")`: contrast_ratio_x100 998 (aliased)
  -> 1839 (in the 1700..1900 band), delta 235; `web_wm_modern_shell_spec`
  4/5 -> 5/5.
- Package consumer render (session draw IR snapshot selection ->
  `widget_tree_to_draw_ir_with_theme` -> CPU Engine2D, demo_kitchen_sink at
  320x240, 67 commands):

  | state | snapshot id / family | px0 | frame hash |
  |---|---|---|---|
  | aetheric_dark | aetheric_dark / aetheric | 0xFF1E1E1F | 16304872557013199116 |
  | glass_dark, alias removed, no package | glass_dark / (empty) | 0xFF1E1E1F | 16304872557013199116 (same as aetheric) |
  | glass_dark package | glass_dark / aetheric | 0xFF1C1C20 | 7967233065849302787 |

  `os.compositor.browser_backend` background: aliased 0xFF0E0E10 -> package
  0xFF0A0A0F (that software path paints only the background for these
  examples, so it shows the palette, not widgets).
- Headless Chromium (playwright chromium_headless_shell-1255),
  `write_wm_modern_preview_html(..., "glass_dark")` at 1280x800: computed
  `--ui-bg`/`--ui-fg` `#0A0A0F`/`#F5F5F7`, body text `rgb(245,245,247)`,
  `.wm-window` background `rgba(30,30,35,0.72)` (glass surface_primary);
  aliased run had `#0e0e10` / text `#cdd6f4`. Screenshot sha256 prefix
  aliased `9c42652d82d30f64` -> package `3cdc255596bd818b`. The page body is
  transparent, so no single screenshot pixel equals `#0A0A0F`.
- Regression set run serially before and after: identical failing example
  names (all pre-existing): web_theme_css_authority 1/6,
  wm_theme_bootstrap_contract 1/12, wm_chrome_theme 1/10, wm_html 0/2,
  color 0/50, host_wm_runtime_loop 0/2; green: glass_css_output 29/29,
  token_resolution 49/49, glass_obsidian_theme 34/34.

Coordination: `work/wm-gui-os-liquid-theme-20261126` (unmerged) also edits
`theme.sdn`; `git merge-file` merges the two cleanly, but whichever lands
second must refresh the aetheric_dark generated manifest sha again.

Still open, separately: the quality report reads the FIRST `--ui-bg`; the
effective `--ui-accent` in the glass preview computes to `#64d2ff` (a later
declaration than the package's `#0A84FF`).

## Review fix: fluid_light generated snapshot regenerated

Registering glass_dark edits `config/themes/theme.sdn`, which is in every
package's source manifest, so the SimpleOS-installed
`src/lib/common/ui/generated/fluid_light_theme_snapshot.spl` (manifest
`0e67202d…`) no longer matched the hosted package (`d2143594…`). The file was
regenerated from `theme_package_render_snapshot("fluid_light")` with a
throwaway emitter that reproduces the old file byte-for-byte from the old
snapshot (format proof), then re-run on the live package. The reviewer's
`manifest.sh` recompute gives `d2143594…` for this tree and `0e67202d…` at the
file's generating commit `2e713257eff`, so the manifest was valid when written.

Material hash `9b37137f…` -> `18bb5010…` is pre-existing drift, not this
change: composed CSS is byte-identical (23,984 bytes) and the only differing
material fields are the RGB channels of `rgba()` inputs, which the old file
stored as white with the correct alpha:

| field | CSS source | old | live |
|---|---|---|---|
| border_rgba | `--app-border: rgba(113,119,134,0.18)` | `0x2EFFFFFF` | `0x2E717786` |
| secondary_text_rgba | `--ui-dim: rgba(65,71,85,0.78)` | `0xC7FFFFFF` | `0xC7414755` |
| active shadow | `rgba(0,68,160,0.16)` | `0x29FFFFFF` | `0x290044A0` |
| inactive shadow | `rgba(0,68,160,0.12)` | `0x1FFFFFFF` | `0x1F0044A0` |

Fluid CSS and `_argb_from_css` logic are unchanged since `2e713257eff` (only
trim/starts_with helper renames), so the white channels came from the
binary that generated the file, not from the source; the live values are the
CSS-correct ones. New `theme_package_spec` example pins fluid manifest,
material, border and secondary-text parity: red 20/21 -> green 21/21.
`simpleos_wm_theme_bootstrap_spec` 3/3 before and after;
`wm_theme_bootstrap_contract_spec` 1/12 before and after, identical failing
names (pre-existing, source-text assertions).

## Follow-up 2026-11-26: accent override and carried-over aetheric paint

Root cause of `#64d2ff`: every WM root (`html.spl`, `html_modern_preview.spl`,
`simple_web_window_renderer.spl`) hardcoded `data-wm-accent="blue"`, and the
generated CSS rule `:root[data-wm-accent=blue] { --ui-accent: #64d2ff }` is
more specific than the package `:root` block. `wm.js` did the same in the live
page: `_applyAccentPreference` defaulted to the first choice (`blue`) and
wrote `--ui-accent` inline. Fix: a `theme` accent choice (first, the default)
that sets no override and removes the inline properties, so the package
accent wins; the five explicit accents still apply when picked.

The glass package also still carried aetheric-only paint. Replaced with
GlassColorTokens.dark values (`src/lib/common/ui/glass/tokens.spl:108`):
background gradient `#0A0A0F/#0b0d10`, badge and button text `#0A0A0F` (see the contrast table below),
titlebar/menubar `rgba(20,20,25,0.72)` (surface_container_lowest), input,
tab bar and statusbar `rgba(25,25,32,0.72)`, error tint from `#FF453A`,
dialog overlay from the glass background.

Evidence (Chromium headless, `getComputedStyle`, glass_dark preview):

| value | before | after |
|---|---|---|
| `--ui-accent` | `#64d2ff` | `#0A84FF` |
| `--ui-badge-text` | `#061222` | `#F5F5F7` |
| `--app-background-image` | `#0f172a/#1e1b4b/#312e81` | `#0A0A0F/#0b0d10` |
| `--ui-titlebar-background` | `rgba(14,14,16,0.72)` | `rgba(20,20,25,0.72)` |
| `--ui-input-background` | `rgba(19,19,21,0.76)` | `rgba(25,25,32,0.72)` |
| aetheric-only literals in page | 13 | 0 |

Screenshot sha256 prefix `f312c92193d3e84c` -> `c068328fca52c13b`.
`theme_package_spec` 20/20 (new assertion: no aetheric-only literal in the
glass composed CSS), `web_wm_modern_shell_spec` 5/5.

Review follow-up (same day):

- Small-text contrast (WCAG AA 4.5:1). `#F5F5F7` on the accent button was
  3.35:1 and on the `#FF453A` badge 3.13:1. Button and badge text are now
  `#0A0A0F` (the glass background): 5.42:1 and 5.80:1. The rendered WM badge
  rules hardcoded white on `#ef4444` (3.76:1) for every theme; they now read
  `var(--ui-badge-text)` / `var(--ui-badge-background)`, with a `#d70015`
  fallback (5.38:1 with white) for themes without a package.
  `wm_theme_quality_report` gains `button_text_contrast_x100` and
  `badge_text_contrast_x100` from the package tokens (last `.widget-button`
  rule, `--ui-badge-text` over `--ui-accent` / `--ui-error`), and
  `color_checked` requires both >= 450 when the theme has a package. Red
  293/291 with the old tokens -> green; aetheric_dark (11.0/11.1) and
  fluid_light (6.7/6.5) also pass.
- The `theme` accent choice has a `var(--ui-accent)` swatch rule, and the
  static palette and control-center markup in the WM page and preview now
  show `theme` selected as choice 0, with blue as choice 1.
- The default accent changes for every theme, not only glass_dark. That is
  intended and matches Chrome's default: the default follows the theme and an
  explicit pick overrides it. Chromium values from the static preview
  (before / after):

| theme | `--ui-accent` | badge text/fill | theme swatch |
|---|---|---|---|
| glass_dark | `#64d2ff` / `#0A84FF` | white on `#ef4444` / `#0A0A0F` on `#FF453A` | none / `#0A84FF` |
| aetheric_dark | `#64d2ff` / `#adc6ff` | white on `#ef4444` / `#061222` on `#ffb4ab` | none / `#adc6ff` |
| fluid_light | `#64d2ff` / `#0058bc` | white on `#ef4444` / white on `#ba1a1a` | none / `#0058bc` |
| obsidian (no package) | `#64d2ff` / `#89b4fa` | white on `#ef4444` / white on `#d70015` | none / `#89b4fa` |

  In the live page, `wm.js` used to write `#64d2ff` inline for every theme;
  it now removes the inline value for `theme`.
- `web_wm_modern_shell_spec` 5/5, `theme_package_spec` 21/21, and
  `web_api_spec` 13/16 with the same three failures as before.
  Still not updated: the quality inspector's accent-policy preview still
  shows the five fixed colours (static markup, 5-column grid).
