# Stitch Simple-OS Theme Guide

This guide describes the theming system shared between the Simple OS window manager
(WM) and the GUI library. The goal is simple: **every palette value in the compositor
traces back to one token file**, and the GUI library reads the same tokens via its
own typed wrappers. No parallel copies, no drifted literals, and no effort to "sync"
two design systems at review time.

If you're adding a new compositor component or a new GUI widget, the rule is:

> **Never introduce a new color, alpha, radius, or blur literal in compositor code.
> Add a token first, then consume it.**

The rest of this guide exists to make that rule easy to follow.

---

## 1. Source of truth

There are **two twin files**, both in the GUI library, that together form the theme
registry:

| File | Purpose | Consumers |
|---|---|---|
| `src/lib/common/ui/glass_numeric_tokens.spl` | `u64` numeric values (`GLASS_DARK_*`, `GLASS_LIGHT_*`, `GLASS_OBSIDIAN_*`, `GLASS_BTN_*`, `GLASS_ICON_*`, `GLASS_RADIUS_*`, `GLASS_BLUR_*`, surface hierarchy) | compositor (baremetal + hosted), any Simple code that needs ARGB pixels |
| `src/lib/common/ui/glass_tokens.spl` | CSS/text strings (`GlassColorTokens`, `GlassDesignTokens`, `StitchDesignSystem`) with `light()`, `dark()`, `obsidian()`, `celestial_ether()` factories | web UI (`src/app/ui.web/html.spl`), CSS generator (`glass_css.spl`), `theme_sync` round-trip with Stitch cloud |

The twin-file arrangement exists because the compositor runs without an HTML/CSS
layer — it needs `u32` ARGB values to pass directly to `CompositorBackend.fill_rect`
and friends. The CSS twin exists so the web UI and the Stitch round-trip can work
with the same semantics in a CSS-native form. **Both files are kept in sync with
the `theme_sync` skill**, which pulls from the Stitch cloud project and regenerates
the numeric values from the pulled snapshots.

### What's in each token family

`glass_numeric_tokens.spl` groups tokens by theme and by semantic role:

- **`GLASS_DARK_*`** — legacy macOS-style dark glass (surface, elevated, border, accent, text, bg_top/bg_bottom, shadow alpha).
- **`GLASS_LIGHT_*`** — light counterpart of the above.
- **`GLASS_OBSIDIAN_*`** — MD3 dark palette from Stitch project `12496218458601315145`.
  Includes the full MD3 color set (`*_SURFACE_BRIGHT`, `*_SURFACE_DIM`, `*_CONTAINER*`,
  `*_ON_*`, `*_PRIMARY`, `*_SECONDARY`, `*_TERTIARY`, `*_INVERSE_*`, `*_OVERRIDE_*`).
- **`GLASS_GLASS_*`** — MD3 seed colors from Stitch project `14134637940805933672`
  (TONAL_SPOT; Stitch derives the palette at render time).
- **`GLASS_BTN_CLOSE/MIN/MAX`** — macOS traffic-light canonical colors. Use **only
  these** for traffic lights; never re-declare them in decoration code.
- **`GLASS_ICON_*`** — dock/system-bar icon accent colors.
- **`GLASS_RADIUS_*`**, **`GLASS_BLUR_*`**, **`GLASS_SHADOW_*`** — layout/effect scalars.
- **`GLASS_SURFACE_0..4_*`** — the 5-level surface hierarchy (alpha + blur) shared
  between the GUI widget layer and the compositor surface stack.

`glass_tokens.spl` exposes:

- **`GlassColorTokens`** — `light()`, `dark()` (CSS `rgba(...)` strings).
- **`GlassDesignTokens`** — wraps `GlassColorTokens` with typography/radius/shadow/spacing/animation/opacity token groups (reuses `IOSTypographyScale`, `IOSRadiusTokens`, etc.).
- **`StitchDesignSystem`** — the round-trip-friendly form with `obsidian()`, `glass()`,
  `celestial_ether()` factories. This is what `theme_sync` pulls from and pushes to
  the Stitch cloud.

### The three design systems

| Theme | Project ID | Kind | Seed | Status |
|---|---|---|---|---|
| **Obsidian** | `12496218458601315145` | MD3 dark, explicit named colors | `0x001A0830` | **Compositor runtime default** |
| **Glass** | `14134637940805933672` | MD3 dark, TONAL_SPOT (derived) | `0x000A84FF` | legacy compositor default |
| **Celestial Ether** | (see snapshots) | MD3 light | — | light theme |

Snapshots live in `doc/05_design/stitch_snapshots/<project-id>/design_systems/*.sdn`.
Pull the latest from Stitch cloud via `/theme_sync pull`.

---

## 2. Consumption paths

### Window manager (runtime render)

The real runtime render for both hosted macOS WM and baremetal QEMU WM uses
**`GlassConfig`** (`src/os/compositor/glass_effects.spl:21`), a `u64`-typed struct
with three token-driven factories: `GlassConfig.dark()`, `.light()`, and
`.obsidian_dark()`. Each factory builds its fields by reading directly from
`glass_numeric_tokens.spl` — there are no literals in those factories.

`Compositor.glass_config` (`src/os/compositor/compositor.spl`) holds one of these.
The runtime default is:

```spl
glass_config: GlassConfig.obsidian_dark()
```

Per-frame, the compositor lowers this `u64` `GlassConfig` into a narrow-type
**`GlassPortConfig`** (`src/os/compositor/glass_port.spl:13`) with `u32`/`u8`/`i32`
fields, which it passes to the backend drawing helpers (`CompositorBackend.fill_rect`
etc. all take `u32`). The lowering happens in `compositor.spl` around the pure-Simple
render path (look for `val cfg = GlassPortConfig(...)` near the `_render_glass_*_pure`
functions).

`GlassPortConfig` also has `.dark()`, `.light()`, `.obsidian()` static factories
built from the same `glass_numeric_tokens.spl` tokens. These are only used for
contexts that want a token-driven default without threading a live `GlassConfig`
through — today the only such caller is the **boot splash**
(`examples/simple_os/hosted/hosted_wm.spl`, `src/os/compositor/boot_splash.spl`).

#### Decorations and chrome

The simple (non-glass) window frame in `src/os/compositor/decorations.spl` exposes
per-role color accessors — `title_bar_color_focused()`, `border_color_focused()`,
`close_button_bg()`, etc. All of them now read `GLASS_DARK_*` / `GLASS_BTN_*` tokens
and promote to `u32` ARGB via `| ALPHA_OPAQUE`. The single `ALPHA_OPAQUE: u32 =
0xFF000000` constant lives at the top of the file.

`_draw_traffic_lights` for the enhanced glass frame lives in
`src/os/compositor/window_effects.spl`; it uses **intentional artistic variants**
(pink/purple) that are *not* the macOS traffic-light palette. Do not tokenize those
— they are art, not palette. The only traffic-light path that uses the canonical
`GLASS_BTN_CLOSE/MIN/MAX` tokens is `draw_glass_window_frame` (the simple glass
fallback) in `decorations.spl`.

The dock and system-bar chrome lives in `src/os/compositor/desktop_chrome.spl`.
Icon colors come from `GLASS_ICON_*` tokens via per-icon accessor functions
(`icon_term()`, `icon_files()`, …). The `GLASS_DARK_ELEVATED` / `GLASS_DARK_SURFACE`
tokens are used for the system-bar gradient and the clock-bg chip. Other literals
in that file (`0x004080FF` blue wash, `0x00FF6B8A` pink undertone, `0xFFE0E0F0`
chrome text, `0xFFFF3B30` iOS red notification) are **effect tints and status
colors**, not palette, and are intentionally left as literals.

### GUI library (widgets, CSS, web)

- **`src/lib/common/ui/glass_theme.spl`** — `UITheme` factory functions
  `glass_light()`, `glass_dark()`, `glass_obsidian_dark()` that build the widget
  layer theme from `GlassColorTokens` / `GlassDesignTokens`.
- **`src/lib/common/ui/glass_css.spl`** — CSS custom-property generator
  (`glass_tokens_to_css()`) for the web UI.
- **`src/app/ui.web/html.spl`** — imports `GlassColorTokens` directly for the web
  surfaces (HTML-rendered UI).

### Stitch round-trip

- **Pull**: `/theme_sync pull` fetches the active design system from the Stitch
  cloud project, writes a snapshot `.sdn` under
  `doc/05_design/stitch_snapshots/<project-id>/design_systems/`, and (when the
  palette has changed) regenerates the numeric twin in
  `src/lib/common/ui/glass_numeric_tokens.spl`.
- **Push**: `/theme_sync push` takes the local `StitchDesignSystem` and
  `stitch_design_md.sdn` and updates the Stitch cloud project.
- The `theme_sync` skill definition is at `.claude/skills/theme_sync.md`.

---

## 3. Rules for new components

1. **No new palette literals in compositor code.** If you find yourself typing a
   hex RGB value, stop and look for an existing token in `glass_numeric_tokens.spl`
   first. If one exists, use it. If one doesn't, either (a) add the token to
   `glass_numeric_tokens.spl` + its CSS twin in `glass_tokens.spl`, or (b) accept
   the literal only if it's an **effect tint** (a blending overlay, not a palette
   color) — and comment why.

2. **Never redeclare an existing token.** Before adding `GLASS_FOO = 0x123456`, grep:
   ```
   Grep -n "0x123456" src/lib/common/ui/glass_numeric_tokens.spl
   ```
   and also
   ```
   Grep -n "GLASS_FOO" src/lib/common/ui
   ```

3. **GUI lib code uses the CSS twin (`GlassColorTokens`).** Compositor code uses the
   numeric twin (`GLASS_*` constants). Don't mix.

4. **Traffic light colors live only in `GLASS_BTN_CLOSE/MIN/MAX`.** Do not re-introduce
   `0xFFFF5F57`/`0xFFFEBC2E`/`0xFF28C840` literals. Any drift fix belongs in the token
   file.

5. **Effect tints are not palette.** Blend overlays with arbitrary hue (`0x004080FF`
   blue wash, `0x00FF6B8A` pink undertone) or opacity-mask whites/blacks
   (`0x00FFFFFF`/`0x00000000`) are fine as literals — they're rendering constants,
   not colors anyone picks from a design system.

6. **If you need a new theme**, add a new family of `GLASS_<theme>_*` tokens to
   `glass_numeric_tokens.spl`, mirror in `glass_tokens.spl` via a new
   `StitchDesignSystem.<theme>()` factory, add `GlassConfig.<theme>()` and
   `GlassPortConfig.<theme>()` factories, and optionally wire into the `T`-key
   toggle. Do **not** fork the WM or GUI lib theme code.

---

## 4. Switching themes at runtime

- The hosted WM (`examples/simple_os/hosted/hosted_wm.spl`) starts with the
  compositor default, currently `GlassConfig.obsidian_dark()`.
- Pressing **`T`** in the running WM toggles between dark and light via
  `compositor.spl`'s T-key handlers. (The cycle currently flips between
  `GlassConfig.dark()` and `GlassConfig.light()` — extending it to include
  `obsidian_dark()` is a small, bounded change if you want it.)
- The boot splash uses a `GlassPortConfig.*` factory chosen at the call site in
  `hosted_wm.spl`. Keep this matched to the compositor default so there's no visual
  pop when the splash hands off to the desktop.

To change the runtime default:
1. Edit `src/os/compositor/compositor.spl`, field `glass_config:` in the
   `Compositor` constructor (search for `GlassConfig.obsidian_dark()`).
2. Edit `examples/simple_os/hosted/hosted_wm.spl`, `val splash_cfg = ...`, to match.
3. Rebuild and relaunch.

---

## 5. Troubleshooting

**A color looks wrong.** First, grep the compositor code for the literal:

```
Grep -n '0xFFAABBCC' src/os/compositor
```

If the literal appears anywhere under `src/os/compositor/`, it's almost certainly
a drifted token that slipped in before this guide. Replace it with the matching
`GLASS_*` token. If you can't find a matching token, the drift may be bidirectional —
check the `glass_numeric_tokens.spl` value against the Stitch snapshot:

```
doc/05_design/stitch_snapshots/<project-id>/design_systems/<theme>_active.sdn
```

The snapshot is the ground truth pulled from Stitch cloud.

**Two tokens drifted from each other.** `glass_numeric_tokens.spl` and
`glass_tokens.spl` are supposed to stay in sync — `theme_sync` regenerates the
numeric twin when the CSS twin changes. If they diverge, run `/theme_sync pull`
to re-sync from Stitch cloud.

**`GlassConfig` vs `GlassPortConfig` confusion.** `GlassConfig` is `u64` and is the
runtime theme type. `GlassPortConfig` is the `u32`/`u8`/`i32` narrow-type lowering
built per-frame from `GlassConfig`. If you need a compile-time static default, use
`GlassPortConfig.dark()/.light()/.obsidian()`. If you need the live runtime theme,
read `Compositor.glass_config`.

**Boot splash doesn't match the desktop theme.** Check that the `hosted_wm.spl`
`splash_cfg` factory matches the compositor's default `GlassConfig` factory. They
need to move together.

---

## 6. File index

- Source of truth: `src/lib/common/ui/glass_numeric_tokens.spl`, `src/lib/common/ui/glass_tokens.spl`
- Stitch round-trip: `src/app/cli/theme_sync.spl`, `src/lib/common/ui/theme_sync_sdn.spl`, `src/lib/common/ui/theme_sync_diff.spl`
- Stitch snapshots: `doc/05_design/stitch_snapshots/<project-id>/design_systems/*.sdn`
- Stitch reference extract: `doc/05_design/stitch_design_system.md`
- Compositor runtime theme: `src/os/compositor/glass_effects.spl` (`GlassConfig`), `src/os/compositor/compositor.spl` (holds `glass_config`, sets default)
- Compositor lowered theme: `src/os/compositor/glass_port.spl` (`GlassPortConfig` + factories)
- Compositor chrome: `src/os/compositor/decorations.spl`, `src/os/compositor/window_effects.spl`, `src/os/compositor/desktop_chrome.spl`, `src/os/compositor/boot_splash.spl`
- GUI library consumers: `src/lib/common/ui/glass_theme.spl`, `src/lib/common/ui/glass_css.spl`, `src/lib/common/ui/design_tokens.spl`
- Web consumer: `src/app/ui.web/html.spl`
- Theme-sync skill: `.claude/skills/theme_sync.md`
- Stitch skill: `.claude/skills/stitch.md`
