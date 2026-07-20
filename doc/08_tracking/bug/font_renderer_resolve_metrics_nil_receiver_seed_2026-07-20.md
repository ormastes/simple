# font_renderer: resolve_font_metrics_with_language nil-receiver crash under seed (blocks WM Draw IR composition + widget_draw_ir)

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
