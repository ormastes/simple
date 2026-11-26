# BUG: WM theme quality contrast for glass_dark reads a palette the cascade overrides

Status: OPEN (2026-11-26). Owner decision needed.
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
