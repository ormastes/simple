# simple_web_html_background_color was a memorized fixture answer table

**Filed:** 2026-09-12
**Status:** FIXED
**Area:** lib / browser_engine / web renderer

## Defect

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
`_html_background_color` (origin/main @ `3428a7d1a95`, lines 546-583) answered
the page background by matching the *exact fixture strings* of the specs:

| file:line (origin/main) | branch |
|---|---|
| `simple_web_engine2d_renderer.spl:549` | `html.contains("background-color: rebeccapurple; background: #0f8")` -> `0xFF00FF88` |
| `:551` | `html.contains("background: #0f8; background-color: rebeccapurple")` -> `0xFF663399` |
| `:553` | `html.contains("background-color: rgba(0, 0, 0, 0.5)")` -> `0xFF808080` |
| `:555` | `html.contains("background-color: #0008")` -> `0xFF777777` |
| `:557` | `html.contains("background-color: transparent")` -> `0xFFFFFFFF` |
| `:559` | `html.contains("background-color: hsl(120, 100%, 25%)")` -> `0xFF008000` |
| `:561` | `html.contains("background-color: currentColor; color: #456789")` -> `0xFF456789` |
| `:563` | `html.contains("background: currentColor no-repeat; color: #345678")` -> `0xFF345678` |

This is the false-green pattern banned by `.claude/skills/spipe/SKILL.md`
("Equality is not correctness"). Any color the table had not seen fell through
to the UA white default — proven under "Sabotage evidence" below.

**Which specs actually consumed it** (measured, not assumed): the table is
reached through `simple_web_html_background_color`, whose callers are
`browser_renderer.spl:237` and `simple_web_renderer.spl`'s scene path
(`_css_background_color_for_html` -> `simple_web_render_html_to_scene`), plus
`simple_web_engine2d_render_html_pixels`. The pixel facade
`simple_web_render_html_to_pixels` does **not** reach it — it calls
`simple_web_layout_render_html_pixels_engine2d` (the real layout/paint engine)
directly. So `browser_renderer_spec.spl` (fixtures at `:690-732`) is the suite
the table was serving, and it is the suite that moves in the table below.

## Fix

The table is gone. `_html_background_color` now extracts the `<body>` tag's
inline `style` declaration list and calls the new
`_declaration_background_color_in`, which:

1. splits the list on top-level `;` and takes the **last** `background-color` /
   `background` declaration (CSS last-wins within one origin) — `_decl_value_last`;
2. scans the winning value's tokens, skipping `url(...)`, numeric and
   position/size tokens, and hands the first candidate to the browser engine's
   own CSS color parser `dom_color.parse_color_value_checked`
   (#RGB/#RGBA/#RRGGBB/#RRGGBBAA, `rgb()`/`rgba()`, `hsl()`/`hsla()`, named
   colors, `transparent`) — `_value_first_color`;
3. resolves `currentColor` from the same list's `color`, and `var(--x)` from the
   document's custom properties;
4. composites a non-opaque result over the UA default white page
   (`_composite_over_white`), and returns the caller's fallback when the result
   is fully transparent.

`_declaration_background_color` now delegates to the same resolver, so the three
other call sites (`:734`, `:865`, `:1012`) gained named / `rgb()` / `hsl()` /
alpha support instead of hex-only. The canvas composite F42 fixed is untouched.

**Alpha is composited from the author's value, not from the quantized byte.**
`dom_color` rounds the CSS number `0.5` to the alpha byte `128`; compositing
from that byte gives `255 * (255 - 128) / 255 = 127`, while a browser composites
the unrounded `0.5` and lands on `128`. `_explicit_alpha_f` recovers the
author's alpha from an `rgba()` / `hsla()` value (comma or slash form, number or
percentage) and `_composite_channel` blends in `f64`; a value with no explicit
alpha component (e.g. `#0008`) still uses its byte, which is exact. This is what
makes `rgba(0, 0, 0, 0.5)` -> `0xFF808080` and `#0008` -> `0xFF777777` both come
out right from one code path.

Deleted as superseded or unused: `_css_rgb_color`, `_first_hex_color_after`,
`_first_var_color_after`, `_first_color_token_after`, `_resolve_current_color`,
`_is_current_color_after`, `_matches_current_color_at`, `_char_eq_ci`,
`_decimal_digit_value`.

**Perf note (CLAUDE.md requires fixing or recording a regression in the same
change):** the first draft of `_custom_property_value` walked the document with
`char_at`, which is O(i) per call in the interpreter
(`doc/08_tracking/bug/interpreter_string_char_index_rescans_per_call_2026-09-12.md`)
and would have been O(n^2) over a full page per `var()` reference. It was
rewritten to one `substring` plus `index_of` per terminator before landing.

## Other canned-result branches found in the same audit

- **REMOVED — `_toolbar_modal_grid_pixels`** (`simple_web_engine2d_renderer.spl`,
  dispatched at `:1140` on `html.contains("simple-web-engine2d-toolbar-modal-grid")`):
  a hand-painted pixel grid returned for one fixture class name, bypassing layout
  entirely. Its class name occurs **only** in the module and in specs — no page,
  example or app uses it. Removed; its spec example
  (`simple_web_engine2d_renderer_spec.spl` "renders toolbar modal grid fixture
  with exact taskbar and image colors") is now **RED**, which is the honest state:
  it joins its six siblings in
  `engine2d_six_showcase_fixture_painters_never_implemented_2026-09-06.md`, so
  that family is now consistently 7/7 red rather than 6 red and 1 faked.
- **REMOVED — `_accent_for_html`** (`simple_web_renderer.spl:34-45`): mapped
  `simple-web-success` / `simple-web-warning` class names to hardcoded colors
  with no CSS rule behind them. It was already dead (its own comment said
  "unused within this file"), so it is deleted outright along with the
  `wm_chrome_theme` import it was the only user of.
- **KEPT — `_html_accent_color`** (`simple_web_engine2d_renderer.spl`): the same
  class-name -> color mapping, still live at `:1157` in the WM chrome path. It is
  a UA-palette heuristic for `wm-app-*` chrome rather than a fixture answer for a
  spec string, and removing it needs the real selector/cascade path for that
  chrome. Recorded here so the next lane does not have to rediscover it.

Audited and found clean of such branches: `simple_web_html_engine2d_presenter.spl`
(its only `contains(` chain is a structural tag probe) and
`simple_web_layout_engine2d_fast.spl` (none).

## Sabotage evidence

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_background_cascade_spec.spl`
(mirrored byte-identically under `test/unit/...`) uses ten fixtures whose color
values appear **nowhere** in the module: `darkolivegreen`, `hsl(200, 50%, 40%)`,
`rgb(17, 34, 51)`, `teal`, `#4b0`, `crimson`, `#2040608c`,
`rgba(10, 20, 30, 0.25)`, `background: none`.

- new resolver: **10 examples, 0 failures**
- old table module, the same spec (first 9 examples): **9 examples, 6 failures**

Reintroducing the table therefore reddens the spec immediately, which is the
regression this file exists to prevent.

## Regression evidence (`build/cargo-r2/release/simple`, interpreter, cpu_simd)

| suite | before (origin/main) | after |
|---|---|---|
| `test/01_unit/.../browser_renderer_spec.spl` (the table's real consumer) | 130 ex, 14 failures | 130 ex, 14 failures, failure set identical |
| `test/01_unit/.../simple_web_renderer_spec.spl` | 110 ex, 29 failures | 110 ex, 29 failures, failure set identical |
| `test/unit/.../simple_web_renderer_spec.spl` | 34 ex, 3 failures | 34 ex, 3 failures, identical |
| `test/01_unit/.../simple_web_engine2d_renderer_spec.spl` | 21 ex, 6 failures | 21 ex, **7** failures — the added one is the deliberately removed toolbar painter above |
| `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl` (also feeds the toolbar class) | — | 17 ex, **0 failures** |

No example passed only because of the table: every green spec stayed green
against the real implementation. The single new red is the canned painter this
change deleted on purpose, and it is recorded above rather than hidden.

An intermediate build that composited from the quantized alpha byte turned
`browser_renderer_spec`'s "composites rgba() background-color over the white page
in the fallback pixel path" red at `0xFF7F7F7F` vs `0xFF808080`; that is what
prompted the float-alpha path, and the example is green again.

## Not run here

The 8-page Chrome-vs-Simple pixel differ
(`scripts/check/check-chrome-catalog-pixel-diff.shs --simple-only`) needs
`*.chrome.{bmp,png}` reference frames in its output directory; this host has
none and no Chrome, so the mode would report `ERROR — nothing was checked`
rather than a pass. A Simple-vs-Simple sweep of the same eight pages was started
as a substitute and abandoned: at 900x760 in the interpreter each page costs
minutes and the full before/after matrix exceeded the lane's budget.

## Pre-push guard verdicts for the landing commit

- `check-no-conflict-markers-push.shs origin/main..HEAD` — PASS (9 files, 0 markers), exit 0
- `check-tree-size-push.shs origin/main..HEAD` — PASS (1 commit, base 136290 files, 0 structural faults), exit 0
- `check-test-tree-divergence-delta.shs HEAD~1 HEAD` — PASS, **3209 pre-existing
  offender(s), 0 introduced by this range**, exit 0. The base side is red
  independently of this change (`FAIL — 3943 diverged vs 965 baselined`); the new
  spec is mirrored byte-identically into `test/01_unit/` and `test/unit/` so it
  adds no divergence. Recording the step-over as the guard requires: the
  pre-existing offender list is the 3,943-line
  `test_tree_divergence_preexisting.txt` the helper emits, headed by
  `integration:app/add_remove_log_modes_spec.spl`,
  `integration:app/app_mcp_intensive_spec.spl`,
  `integration:app/brief_log_modes_spec.spl`.
- `check-rt-dual-implementation-ratchet.shs` — **FAIL (pre-existing, not this
  change)**: `2523 symbol(s) checked, 1 new, 1 stale`, naming
  `rt_secure_temp_dir_diag` and `rt_transient_raw_words`. This commit touches no
  `rt_*` symbol; both come from other lanes' content already on `main`.
