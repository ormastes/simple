# Silent interpreter fallback poisons entire callee tree when engine is called from gui_window frame

**Date:** 2026-08-06 (updated 2026-08-07)
**Status:** OPEN — unverified. 2026-08-07 pass built a probe that confirms the
general unresolved-extern-symbol whole-module fallback IS loud when it fires,
but could NOT confirm that mechanism is what fires on this bug's actual
`gui_window.spl`/`--open` path (a `SIMPLE_JIT_STRICT=1` text-mode check argues
against it). Whether the real repro's fallback is silent remains untested —
see "2026-08-07 update" below before trusting either the original Severity
line or an earlier same-day draft of that update that overclaimed a refutal.
**Severity:** High (perf cliff itself is real and reproduced via workaround
diff; silence claim status: unresolved)

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

## 2026-08-07 update — probe built, general mechanism is loud, THIS bug's trigger still UNVERIFIED (corrected after advisor review)

Follow-up lane (per `doc/09_report/ui/perf/jit_silent_interp_fallback_status_2026-08-07.md`,
which left this specific caller-module-frame variant unchased). Built a
minimal, isolated probe in scratch (kept in its own files per repo memory —
one unsupported op anywhere silently demotes the whole program, so each
probe is a separate file):

- `probe_callee.spl`: `expensive_work(n)` — tight arithmetic loop, no
  imports, cheap oracle for JIT-vs-interpreter (JIT ~339ms for n=50,000,000
  vs interpreted ~1000ms+ for the same n, and the two engines are also
  distinguishable directly via the diagnostic text, not just timing).
- `probe_baseline.spl`: calls `expensive_work` with no `gui_renderer`
  import anywhere in the program. Result: **339ms, clean JIT, zero
  diagnostic output.**
- `probe_via_gui.spl` / `probe_gui_only.spl`: same callee, but the file
  additionally does `use nogc_sync_mut.ui.gui_renderer.{GuiRenderer,
  GUI_EVT_NONE, GUI_EVT_CLOSE}` at module level (the same import
  `gui_window.spl` has) — **without ever calling anything from it**. Result
  reproduced on every run:

  ```
  [jit-fallback] unresolved external symbol 'subsys_from_scope': whole module
  dropped to the interpreter (expect ~100-1000x slowdown). Set
  SIMPLE_JIT_STRICT=1 to turn this into a hard error.
  [INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
  compile: Module error: unresolved external symbol 'subsys_from_scope'
  would NULL-jump in JIT; deferring to interpreter
  via_gui_frame result=149999997 elapsed_ms=1043
  ```

**Follow-up discriminator tests (after advisor review flagged the first pass
as overclaiming) exposed that the probe's trigger and the real bug's
trigger are probably NOT the same thing:**

- `SIMPLE_JIT_STRICT=1 bin/simple run src/app/browser/main.spl
  simple://home` (text mode, no `--open`) ran for the full 60s internal
  CPU-watchdog budget and was killed by the watchdog, **not** by a strict
  unresolved-symbol hard error. `SIMPLE_JIT_STRICT=1` converts exactly the
  `subsys_from_scope`-class failure into an unconditional printed hard
  error (`exec_core.rs` catch-site comment: "propagate as a real, printed,
  non-zero-exit error instead of falling back... for this class of
  failure only"). No such error appeared. This means the browser's real
  text-mode call graph does **not** hit the unresolved-`subsys_from_scope`
  path at all, even though `main.spl:10` unconditionally imports
  `app.browser.gui_window` (which imports `gui_renderer`, same as the
  probe). So the probe's trigger fires on strictly less than what the
  probe's import alone would predict — something about the fuller
  program's module set avoids it (plausibly: some other already-imported
  module registers/provides `subsys_from_scope` in the full browser but
  not in the 3-line scratch program; not confirmed).
- Timing is **not** a reliable engine oracle for `probe_callee.spl`'s tight
  arithmetic loop specifically: forcing the interpreter explicitly
  (`SIMPLE_EXECUTION_MODE=interpret`) on `probe_baseline.spl` gave
  **482ms**, statistically the same as the JIT run (**533ms**) — not the
  100-1000x the `[jit-fallback]` message itself warns about. So the
  1043ms seen for `probe_via_gui.spl` cannot be read as "confirmed
  interpreted at expected magnitude" from timing alone; the only reliable
  signal in this probe is the **diagnostic text itself** (which the
  interpreter-forced run does NOT print, and the fallback run does),
  not the wall-clock ratio. This specific tight loop is apparently cheap
  enough that this interpreter's overhead per iteration doesn't show the
  claimed magnitude — consistent with the original report's own framing
  that the severe multiplier is specific to the browser's
  call/allocation-heavy DOM/CSS/layout/paint pipeline, not a property of
  "interpreted" in general.
- Attempted the cheap direct discriminator on the real repro:
  `SIMPLE_JIT_STRICT=1 bin/simple run src/app/browser/main.spl --open`
  under an 85s external timeout. No diagnostic fired before the watchdog
  killed it; this sandbox has no `DISPLAY`/Xvfb, so it's unclear whether
  the run ever reached `run_browser_window_gui`/`GuiRenderer.create`
  within the budget, or reached it and hung elsewhere (e.g. in
  `GuiRenderer.create`'s window-system probe, not the render). Inconclusive
  — needs a display-equipped harness (Docker+Xvfb, as the original repro
  used) and a longer or better-instrumented budget to settle.

**Revised findings (supersedes the same-day draft above written before
these checks):**

1. **General mechanism confirmed loud, but NOT confirmed to be this bug's
   mechanism.** The `[jit-fallback]` / `[INFO] JIT compilation failed,
   falling back to interpreter` diagnostics at
   `src/compiler_rust/driver/src/exec_core.rs:959` and `:1263` do fire
   reliably and loudly whenever an unresolved-extern-symbol whole-module
   fallback actually occurs (proven directly, 3/3 probe runs). What was
   **not** established is that this is what happens on the real
   `gui_window.spl` / `--open` path — the text-mode strict-mode check
   above argues against the same trigger applying uniformly to the
   browser's real import graph, so "same root cause as the original
   slowdown" from the earlier draft of this update is **withdrawn as
   unsupported**.
2. **The original "no diagnostic emitted" claim is still UNVERIFIED, not
   refuted.** No session (this one included) has captured stderr from an
   actual `--open` run that reaches the slow render and checked it for
   `[jit-fallback]` text. That remains the one measurement that would
   settle this bug directly.
3. **Third possibility (level-gated diagnostic, off by default) was not
   ruled out either** — not investigated this pass; the diagnostics found
   here print unconditionally (no env-gate observed in the code read), so
   if the real bug's mechanism differs from this probe's, whether ITS
   diagnostic (if any) is gated is still open.

**Conclusion / next step:** No code change made — correctly so, since the
visibility gap this bug reports has neither been confirmed nor refuted for
its actual trigger. The one decisive, still-unperformed test: re-run the
original Docker+Xvfb `--open` repro (or a cheaper synthetic one that
actually reaches `GuiRenderer.create` + the real
`browser_engine_pixels_at` call from inside `gui_window.spl`'s frame, with
`SIMPLE_JIT_STRICT=1` set and stderr captured to a file) and grep that file
for `jit-fallback`/`falling back to interpreter`. This session's probes
(`probe_callee.spl`, `probe_baseline.spl`, `probe_via_gui.spl`,
`probe_gui_only.spl`, kept in scratch) are reusable as a template for that
follow-up but are not themselves proof either way for this specific bug.
