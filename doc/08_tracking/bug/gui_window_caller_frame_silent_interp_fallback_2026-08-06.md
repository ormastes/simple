# Silent interpreter fallback poisons entire callee tree when engine is called from gui_window frame

**Date:** 2026-08-06
**Status:** OPEN (workaround shipped in `src/app/browser/main.spl` / `gui_window.spl`)
**Severity:** High (silent ~10-50x slowdown, no diagnostic emitted)

## Symptom

`bin/simple run src/app/browser/main.spl --open` never finished a 64x36
`render_html_to_pixel_array` render inside an 1800s budget (4 attempts,
container + host), while the *identical* render — same function, same
arguments, same page, same binary, same env — completes in ~45-60s when
reached through the text-mode call chain.

## Isolation matrix (measured 2026-08-06, same binary, same page, 64x36)

| Entry chain | Wall | User CPU | Result |
|---|---|---|---|
| host, text mode (`render_browser` -> ... -> `browser_engine_pixels_at`) | 44.7s | 38.6s | 72 px painted |
| container, text mode | 60.6s | 42.8s | 72 px painted |
| container, text mode + `DISPLAY` + `SIMPLE_GUI=1` | 55.6s | 39.3s | 72 px painted |
| container, `--open` (`run_browser_window_gui` -> `browser_engine_pixels_at`) | >1620s, killed | >300s and climbing | never reached window |
| container, `--open` AFTER hoisting the render into `main()` | **59s to window on screen** | — | real frame presented |

Container env, `SIMPLE_GUI=1`, and `DISPLAY` are each exonerated by rows 2-3.
The only remaining variable is the **calling frame**: rendering from
`gui_window.spl` (which imports `nogc_sync_mut.ui.gui_renderer`, an
extern/dlopen-heavy module) runs the whole engine ~10-50x slower than the
same call from `render_adapter.spl`'s chain. Uniform slowdown across the
entire run (log line emission rate ~10x slower from the first line) is the
tree-walk-interpreter signature, not a hot-spot.

## Suspected mechanism

JIT lowering of `run_browser_window_gui` (or something in its
`gui_renderer` import context) fails silently -> the function executes in
the tree-walk interpreter -> **every callee, including the entire
DOM/CSS/layout/paint pipeline, also executes interpreted**. Related, same
import chain: an ad-hoc entry importing only `gui_window`/`render_adapter`
produced a *fatal* `error: semantic: variable _web_budget_clock not found`
(module-level `val` registration order), suggesting the shipped path hits
the same lowering failure non-fatally and falls back instead. See
`reference_silent_interpreted_fallback_hir_unknown_variable` and
`reference_module_level_let_not_preregistered_order_dependent` (memory
notes) for the two prior instances of each half of this mechanism.

## Workaround (shipped)

`main.spl` renders the pixels itself (its branch demonstrably JITs) and
passes the ready `[u32]` buffer into `run_browser_window_gui(url, w, h,
pixels)`; the window function now only creates/presents/polls, which is
cheap even when interpreted. Verified end-to-end under Docker+Xvfb: window
`"Simple Browser - simple://home"` on screen with real glyph pixels in 59s.

## What a real fix needs

1. The fallback must not be silent: one level-gated (default-on, once per
   function) diagnostic naming the function that failed JIT lowering and
   why.
2. Root-cause the lowering failure for the `gui_window` ->
   `gui_renderer` import context (`_web_budget_clock` registration order is
   the lead).
3. A regression probe: time the same engine call from both caller modules;
   fail if the ratio exceeds ~3x.
