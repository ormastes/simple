# font_renderer: resolve_font_metrics_with_language nil-receiver crash under seed (blocks WM Draw IR composition + widget_draw_ir)

**Status:** PARTIALLY MITIGATED, still OPEN 2026-07-20 (root-fix lane,
worktree `/tmp/wt_ttfcrash`, pinned base
`42ebf97e577268703098d7c17d862e74cc15c86a`). **Do not read this as fixed.**

- A real, root-caused bug in `_font_mutex_acquire`/`_font_mutex_release`
  (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) is confirmed and
  its hard crash is mitigated **on the `bin/simple run` evaluator only** — see
  "Mutex bug (run-path, mitigated)" below.
- **This is NOT what blocks `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
  under the actual `bin/simple test` command**, which is the deliverable this
  bug doc is about. Probe evidence (below, "Actual bin/simple test blocker")
  shows the real spec crashes earlier and elsewhere: inside
  `validate_selected_font_asset` (`src/lib/common/encoding/font_registry.spl:514`),
  called from `FontRasterizer._load_selected_bytes`
  (`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:176`), reached from
  `FontRenderer.try_load_selected_bytes` — well before any mutex code runs.
  `font_renderer_spec` still fails with `Passed: 0 / Failed: 1` after this
  pass's changes, identical in shape to before.
- Project note for future readers of this doc: `simple test` (SSpec) uses a
  **different evaluator** than `simple run`. A fix verified only via `run`
  does not establish anything about the `test` path. This doc originally (and
  wrongly, for one intermediate revision) claimed "FIXED" based on `run`-only
  evidence; corrected here after adding evaluator-matched probes.

## Mutex bug (run-path, mitigated)

Confirmed via minimal isolated repros (no font code) and gdb: the shared
mutex-facade helpers `_font_mutex_acquire`/`_font_mutex_release` (top of
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`), used by every lock in
this file (`_resolved_font_metric_lock`, `_browser_default_font_lock`,
`_font_atlas_dependency_generation_lock`), used to unwrap their `Mutex?`
parameter with `current ?? mutex_new(0)` into a single `val`. Under the Rust
seed's `run` evaluator, when the module-level `Mutex?` var's Some-payload came
from the declaration's own `mutex_new(0)` initializer (module-init time), the
`??` operator produced a value that reports `== nil` as `false` but crashes as
"field access on nil receiver" the instant a method (`.lock()`) is called on
it. A local-var-initialized `Mutex?` source unwraps fine via `??`; the
identical module-var-initialized source faulted every time, reproduced via
`bin/simple run` on a standalone script (`FontRenderer.new()` + real TTF load
+ `prepare_text("A"/"", ...)`, which exercises
`_activate_render_config -> _reset_font_atlas ->
_next_font_atlas_dependency_generation -> _font_mutex_acquire`).

Applied mitigation: the three lock module vars now initialize to `nil` at
declaration (matching the file's own already-documented
freestanding/native-build lazy-init intent) and
`_font_mutex_acquire`/`_font_mutex_release` unwrap via a guard clause + `.?`
instead of `??`. This converts the **hard SIGILL crash into a silent
no-op**: gdb + probe evidence on the `run` path shows `.?` still yields a
value that dynamically dispatches as `bool` in this context ("Runtime error:
Function 'bool.lock'/'bool.unlock' not found", non-fatal, execution
continues) — the mutex still does not actually lock/unlock. This is real
value-corruption in the Rust seed's `Mutex?` handling that this pass did NOT
fully root-cause; it only stopped the fatal half. See the "not fully closed"
framing above -- do not treat the `.?`/nil-init change as more than a
crash-to-noop mitigation on a path that, per the next section, is not even
what the actual spec exercises.

## Actual `bin/simple test` blocker (probe-localized, 2026-07-20)

Adding `print()` probes directly in the real spec file and in
`_load_selected_bytes` (temporarily, for diagnosis, not committed) and
running the real `bin/simple test test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
localized the actual crash precisely:

```
✓ rejects nil or stale rasterizers through is_current
SPECPROBE:it-entered
SPECPROBE:path-set
SPECPROBE:renderer-constructed
SPECPROBE:bytes-read len=1708408
PROBE:lsb-enter blob_len=1708408
PROBE:lsb-post-identity id_len=94
PROBE:lsb-pre-validate
<process dies here -- no further probe output, no "renders a selected
face..." example ever runs, Test Summary: Passed 0 / Failed 1, Duration ~67s>
```

So under `bin/simple test`, `FontRenderer.new()`, `file_read_bytes(path)`, and
entry into `_load_selected_bytes` all succeed; the process dies during
`validate_selected_font_asset(ttf_path, blob)`
(`src/lib/common/encoding/font_registry.spl:514`, called from
`FontRasterizer._load_selected_bytes` at
`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:188`). That function does real
1.7MB-blob work (`sha256_u8_hex`, `validate_glyf_font_instance`,
`sfnt_manifest_tables_match`, `sfnt_manifest_names_match`) with no obviously
unsafe .spl statement visible at the call-site level probed. This is
upstream of and unrelated to the mutex code above -- it never gets called
under the `test` evaluator's crash path. Not investigated further in this
pass per scope (avoiding an open-ended native/SFFI-adjacent rabbit hole after
one bounded probe cycle, per the mission's own timeboxing guidance) -- the
next step for whoever picks this up is to probe inside
`validate_selected_font_asset`/`validate_glyf_font_instance` specifically
under `bin/simple test` (not `run` -- the two evaluators disagree here; `run`
reaches `try_load_selected_bytes = true` successfully on the same file, so
this is `test`-evaluator-specific and must be diagnosed on that evaluator).

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
