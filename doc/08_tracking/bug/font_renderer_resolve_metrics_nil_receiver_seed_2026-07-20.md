# font_renderer: resolve_font_metrics_with_language nil-receiver crash under seed (blocks WM Draw IR composition + widget_draw_ir)

**Status:** FIXED 2026-07-20 (root-fix lane, worktree `/tmp/wt_ttfcrash`, pinned
base `42ebf97e577268703098d7c17d862e74cc15c86a`). Root cause confirmed and
fixed in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`
(`_font_mutex_acquire`/`_font_mutex_release`), NOT in
`resolve_font_metrics_with_language`/`_resolve_font_metrics_with_language_config`
directly — see "Actual root cause" below. A SEPARATE, still-open bug
(`font_renderer_glyph_loop_heap_corruption_segv_2026-07-20.md`) now blocks the
full `font_renderer_spec` from reaching a complete green summary; this doc's
own crash no longer reproduces.

## Actual root cause (2026-07-20 update)

Not `resolve_font_metrics_with_language`/`_resolve_font_metrics_with_language_config`
directly — the fault is one level down, in the shared mutex-facade helpers
`_font_mutex_acquire`/`_font_mutex_release` (top of
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`), used by every lock in
this file (`_resolved_font_metric_lock`, `_browser_default_font_lock`,
`_font_atlas_dependency_generation_lock`). They used to unwrap their `Mutex?`
parameter with `current ?? mutex_new(0)` into a single `val`. Under the Rust
seed, when the module-level `Mutex?` var's Some-payload came from the
declaration's own `mutex_new(0)` initializer (module-init time), the `??`
operator produced a value that reports `== nil` as `false` but crashes as
"field access on nil receiver" the instant a method (`.lock()`) is called on
it. Minimal isolated repros (no font code) confirmed this precisely: a
local-var-initialized `Mutex?` source unwraps fine via `??`; the identical
module-var-initialized source faults every time. `resolve_font_metrics_with_language`
just happens to be the first public entry point that reaches
`_activate_render_config` -> `_reset_font_atlas` ->
`_next_font_atlas_dependency_generation` -> `_font_mutex_acquire`, so it was
the symptom's face, not its cause.

Fix: the three lock module vars now initialize to `nil` at declaration
(matching the file's own already-documented freestanding/native-build lazy-init
intent) and `_font_mutex_acquire`/`_font_mutex_release` unwrap via a guard
clause + `.?` instead of `??`. Verified via a from-scratch minimal standalone
repro (`FontRenderer.new()` + real TTF load + `prepare_text("", ...)`, which
exercises exactly this call chain and used to SIGILL — now exits 0).

**Old text below is the original 2026-07-20 filing, kept for history.**

**Status:** OPEN 2026-07-20 — found while adding WM close-lifecycle specs (G2 lane).
**Severity:** Blocking for seed-run WM/GUI specs — `shared_wm_scene_draw_ir_composition` cannot execute at all under the Rust seed; origin/main's own `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` currently aborts at its second example (1 pass printed, then process death, Test Summary `Passed: 0 / Failed: 1`).
**Affected file:** `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (`resolve_font_metrics_with_language`, line ~1635)
**Blast radius:** `src/lib/common/ui/window_scene_draw_ir.spl` (`_wm_draw_ir_text` -> composition), `src/lib/common/ui/widget_draw_ir.spl` (`_default_text*` -> `widget_tree_to_draw_ir`)
**Path:** `bug` track.

## Symptom

Minimal repro (seed `bin/simple run`, repo root, verified at origin/main 6aa78042c14
with a pristine tree):

```
use std.common.encoding.font_registry.{simpleos_default_font_asset_candidate}
use std.nogc_sync_mut.text_layout.font_renderer.{resolve_font_metrics_with_language}

fn main():
    val candidate = simpleos_default_font_asset_candidate()   # ok: "Noto Sans Mono"
    val m = resolve_font_metrics_with_language(candidate.family, "T", 12, "und")
    # -> "runtime error: field access on nil receiver", then SIGILL core dump
```

`simpleos_default_font_asset_candidate()` itself succeeds. The crash is inside
the resolve path (first suspect: `_resolve_font_metrics_with_language_config`
dereferencing a nil registry/glyph record).

## Blast radius (all verified individually)

1. `shared_wm_scene_draw_ir_composition(scene, taskbar, ...)` crashes for ANY
   scene — even borderless-only windows with an empty taskbar and empty clock
   label (the chrome batch also emits text). Bisect: `_wm_draw_ir_desktop_batch`
   fine; `_wm_draw_ir_window_batch` dies in `_wm_draw_ir_text`; a direct
   `_wm_draw_ir_text("t", 66, 19, 0, 28, "T", color, "und")` call dies the same
   way; `wm_chrome_theme()` and `_wm_draw_ir_window_box` are fine.
2. `widget_tree_to_draw_ir_cpu` dies identically even for RECT-ONLY trees
   (button with empty label + progress bar); `common.ui.builder` +
   `compute_layout` alone are fine.
3. On the SSpec test path the crash surfaces as `error: test-runner: no
   examples executed` when the first example touches composition, or as an
   abort mid-file after earlier examples pass (the current
   `window_scene_draw_ir_spec` shape).

Note: `window_scene_draw_ir_spec`'s FIRST example ("retains readable bitmap
text when selected metrics are unavailable") passes, so the invalid-metrics
fallback path works; the crash is on the metrics-resolution path that runs when
a real font candidate is found.

## Not caused by

- The 2026-07-20 WM close-lifecycle changes (G2): reproduced on a pristine
  origin/main tree; no `src/lib`/`src/runtime` file changed in
  93abfa3c6b2..6aa78042c14, so the breakage predates that range's tip motion.

## Blocked tests (explicit skips, not silently dropped)

- `test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl`
  records three skips (composition card census with close/traffic nodes,
  stale-node sweep after close recompose, drawn-rect vs dispatch lockstep) and
  a NOTE for the widget_draw_ir composition specs. Un-skip and implement when
  this bug lands.
