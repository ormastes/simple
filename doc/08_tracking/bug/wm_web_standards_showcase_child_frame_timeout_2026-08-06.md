# wm_web_standards_showcase_gui host gets a real verdict — and it is FAIL (child-frame-timeout), not a hang

**Status:** open. **Severity:** blocks first dynamic pixel-delta verdict for
`examples/06_io/ui/wm_web_standards_showcase_gui.spl` (lane U2, task #96 follow-up).
**Component:** host = `examples/06_io/ui/wm_web_standards_showcase_gui.spl`; child =
`examples/06_io/ui/web_standards_showcase_gui.spl` →
`std.gc_async_mut.gpu.browser_engine.simple_web_renderer.simple_web_render_html_to_pixels_with_engine2d_backend`.

## Summary

U2 reported two attempts (`bin/simple run` with 280s and 900s *external* shell
timeouts) that "never even reached `main()`". That framing is misleading: the
external shell timeout was never the limiting factor. **`bin/simple run` on any
path under `examples/**` applies its own internal watchdog, default 10 seconds**
(`src/compiler_rust/driver/src/cli/examples_safety.rs`,
`DEFAULT_EXAMPLES_TIMEOUT_SECS = 10`, overridable via `SIMPLE_TIMEOUT_SECONDS`,
`0` disables it). Both attempts were killed by that internal 10s watchdog before
either the host or the heavy Engine2D+HTML-layout import graph could finish
loading — regardless of the 280s/900s external timeout, which never got a chance
to matter.

## Reproduction

```
SIMPLE_WM_HEADLESS_CAPTURE=1 SIMPLE_TIMEOUT_SECONDS=1750 \
  bin/simple run examples/06_io/ui/wm_web_standards_showcase_gui.spl
```

This *does* complete — no hang. Real wall time ~3m19s end-to-end (includes
`bin/simple`'s own lint/build wrapper passes, not just the app). The app itself
prints a definitive verdict well before that:

```
wm_web_standards_showcase_host_headless_status=fail
wm_web_standards_showcase_host_headless_reason=child-frame-timeout:missing
```

i.e. the host's own internal deadline for the **spawned child** to produce its
first frame fires before the child gets there — a second, independent internal
timeout, this one inside the wm host/child frame-handshake protocol itself
(`common.ui.wm_app_process_contract`), not the compiler's 10s example watchdog.

## Baseline comparison (already-working `wm_graphics_2d_showcase_gui.spl`)

```
SIMPLE_WM_HEADLESS_CAPTURE=1 SIMPLE_TIMEOUT_SECONDS=350 \
  bin/simple run examples/06_io/ui/wm_graphics_2d_showcase_gui.spl
→ exit 0, real 2m51s
```

Host-side `use` import lists for the two `wm_*_showcase_gui.spl` files are
almost line-for-line identical (both import `Engine2D`, `GuiRenderer`, the same
compositor/process-spawn stack) — the wm host itself is not the cost driver and
the two hosts' load times are comparable (2m51s vs the point at which the web
host's own status line prints, well under a minute of app-visible work; the
remaining wall time in both runs is `bin/simple`'s wrapper passes, not the app).

The actual divergence is in the **spawned child**: `web_standards_showcase_gui.spl`
imports `simple_web_render_html_to_pixels_with_engine2d_backend` (full HTML/CSS
layout stack), `graphics_2d_showcase_gui.spl` does not. The run log for the web
host shows, before the fail verdict:

- `[jit-fallback] HIR lowering error: ... cannot infer field type while lowering
  SimpleWebEngine2DStaticPixelCache.retain_result_for_html: struct
  'SimpleWebLayoutEngine2DReadbackResult' field 'resolved_backend': whole module
  dropped to the interpreter (expect ~100-1000x slowdown)`
- Hundreds of `[font-inherit-trace]` / `[font-style-trace]` / `[rfm]` lines, one
  cluster per styled node — the same per-node cost signature documented in
  `doc/08_tracking/bug/web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
  (~3.2s/node on the interpreted lane, open, multi-session, explicitly
  out-of-scope for this investigation).

**Conclusion: this is the already-documented 3.2s/node interpreted-lane defect
manifesting through the wm-hosted headless-capture path.** The child never
finishes styling all nodes fast enough to paint and hand back a frame before the
host's own child-frame-timeout fires, so the host correctly reports
`child-frame-timeout:missing` rather than hanging silently.

## What this is NOT

- Not an import-time-only issue (comparable import cost to the working baseline).
- Not a defect in U2's Engine2D migration of `wm_web_standards_showcase_gui.spl`
  itself — the host's own status/reason lines are exactly the diagnostic they're
  designed to produce when the child can't keep up, i.e. the harness is working
  correctly and honestly reporting the underlying (separately tracked) perf bug.
- Not fixed here, per scope: fixing the interpreted-lane per-node cost is
  explicitly out of scope for this task and already tracked as its own
  multi-session bug.

## What would unblock a green verdict

Either (a) fix the interpreted-lane per-node styling cost (tracked separately),
or (b) raise the wm host/child frame-handshake deadline enough to tolerate the
current ~3.2s/node cost for this example's node count, as a stopgap — not
attempted here since it would mask rather than fix the underlying defect and
the task scope explicitly excludes touching that bug.

## Verdict status for lane U2 / task #96

No sabotage-test was performed: the oracle currently reports FAIL against
*unmodified* code (`child-frame-timeout:missing`), so there is no green
baseline to sabotage yet. This is nonetheless real, novel information for U2:
previously there was no verdict at all (attempts never got past the compiler's
10s example watchdog); now there is a definitive, reproducible FAIL verdict
whose root cause is understood and cross-referenced to the correct existing bug.

## Re-verified 2026-08-06 (same session, after 4 landed CSS fixes)

Re-ran the exact repro command in this doc's "Reproduction" section, after
this session separately landed 4 real fixes in the same code path:
`apply_css_rules_to_tree`/`process_style_blocks` descendant-style bug,
`SelectorRuleIndex` cascade-order bug, `contain: style` containment wired
into invalidation, and an O(k) property-dispatch fast path. Verdict is
**still FAIL**, same reason string:

```
wm_web_standards_showcase_host_headless_status=fail
wm_web_standards_showcase_host_headless_reason=child-frame-timeout:missing
```

**But the landscape moved.** The host's actual budget for the child's first
frame is `SIMPLE_WM_HEADLESS_CAPTURE_FRAME_TIMEOUT_MS` (default 180000 =
180s, `examples/06_io/ui/wm_web_standards_showcase_gui.spl:543`) — a
different, shorter, and more relevant number than the 270s/580s wall-clock
figures used in `web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`.
Within that 180s window, this run's log shows styling progressed to
`[font-inherit-trace] index=113` of 149 total style-producer nodes
(`[web-style-producer] ... of=149` in this run vs `of=151` in the July doc —
a small, unexplained node-count difference, possibly fixture drift; not
investigated further here) before the host's deadline fired. That is
**113/149 ≈ 76% of nodes styled** in ≤180s, i.e. an upper bound of
**~1.6s/node**, roughly 2x faster than the July doc's ~3.2s/node figure for
the same style-producer loop. This is real, novel, freshly-measured movement
— not a re-citation of the July number — but it is a coarse upper bound (log
line count vs true node count, no per-node timestamp instrumentation added
this pass), not a controlled A/B against a pre-fix baseline, so treat the
~1.6s/node figure as directional, not precise.

**Root cause is unchanged.** The same `[jit-fallback] HIR lowering error:
... SimpleWebEngine2DStaticPixelCache.retain_result_for_html: struct
'SimpleWebLayoutEngine2DReadbackResult' field 'resolved_backend': whole
module dropped to the interpreter (expect ~100-1000x slowdown)` fires in
this run, identical to before — the whole-module interpreted-execution
fallback that `web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
identifies as the primary multiplier is still present and still the
structural blocker. This session's 4 CSS fixes plausibly account for the
~2x apparent speedup (less/cheaper cascade work per node under
interpretation too), but did not touch the interpreter-routing/HIR-lowering
gap, so a ~2x win against a problem the July doc frames as needing ~10x is
not enough to close this lane. No narrow, safe (<20-line) fix was visible
in this pass that is separate from that already-tracked, explicitly
out-of-scope, multi-session interpreted-lane defect — attempting to fix the
HIR-lowering gap itself is exactly the excluded scope for this task, so
nothing was changed here.

**Conclusion:** child-frame-timeout still reproduces, first real dynamic
verdict for this host remains blocked (still no green baseline to
sabotage-test), but the gap narrowed measurably (~76% of nodes styled
within budget now vs an implied small fraction before). Unblocking still
requires either raising `SIMPLE_WM_HEADLESS_CAPTURE_FRAME_TIMEOUT_MS` as a
stopgap (masks rather than fixes, not done) or closing the interpreter-
routing/HIR-lowering gap tracked in the linked bug docs (out of scope here).

## Re-verified again 2026-08-06, later same day — checked against the daemon debug-seed-shadowing fix, still unaffected

This session separately found and fixed
`doc/08_tracking/bug/test_client_debug_seed_binary_shadowing_timeout_2026-08-06.md`
(the light-test-daemon's `simple_binary()` resolver preferred a stray
`target/debug/simple` build over `bin/simple`). Before assuming that fix was
irrelevant here, checked whether `bin/simple run`'s own child-process spawn
path for this host shares any code with it.

**Code-path check: no overlap, confirmed by both source and by `ps`.**
- `simple_binary()` is defined and called only in
  `src/app/test_runner_new/test_runner_client.spl`,
  `src/app/test_daemon/light_daemon.spl`, and `src/app/test_daemon/main.spl`
  (grepped the whole tree; those are the only 3 hits among test/daemon
  infra — the wm example files are not in that list).
- `examples/06_io/ui/wm_web_standards_showcase_gui.spl:launch_showcase_child`
  (lines 394-440) never calls `simple_binary()`. It hardcodes
  `val simple_bin = path_join(repo_root, "bin/simple")` (line 419) and uses
  that same value in **both** spawn branches: the Windows branch
  (`process_spawn_async_env(simple_bin, ["run", showcase_source_path], env)`)
  and the POSIX branch (`process_spawn_async("env", [...env vars..., simple_bin,
  "run", showcase_source_path])`). No fallback chain, no debug-seed candidate,
  no shared helper — completely separate resolution logic from the daemon bug.
- Empirical confirmation while the repro was running: `ps -ef` showed host PID
  963731 and child PID 964447/964449, and `readlink -f /proc/<pid>/exe` for
  both resolved to `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`
  — the same binary both processes' `bin/simple` symlink target, no
  `target/debug/simple` anywhere in the spawn chain.
- Side note, not related to the daemon bug: that release-path binary is
  currently the Rust seed under the hood (prints the seed-banner warning on
  every invocation) per the known, already-tracked, separate Stage 3
  self-host blocker
  (`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
  This affects overall interpreter/JIT performance in general but is orthogonal
  to — and was true both before and after — the debug-seed-shadowing fix, and
  is not evidence that fix regressed anything here.

**Fresh repro run**, exact command from "Reproduction" above, run to completion
(23:12:32-23:15:54, ~3m22s wall, consistent with the ~3m19s figure already in
this doc):

```
wm_web_standards_showcase_host_headless_status=fail
wm_web_standards_showcase_host_headless_reason=child-frame-timeout:missing
```

Unchanged from both prior runs. The `[jit-fallback] HIR lowering error: ...
SimpleWebEngine2DStaticPixelCache.retain_result_for_html: struct
'SimpleWebLayoutEngine2DReadbackResult' field 'resolved_backend': whole
module dropped to the interpreter` line is present again, twice, confirming
the root cause is still the same interpreted-lane fallback. Node progress
this run: `[font-inherit-trace] index=86` of `of=149` at the point the host's
deadline fired — **86/149 ≈ 58%**, lower than the prior run's 113/149 (76%).
This box's load average during this run was 17-27 (`uptime`), materially
higher than typical; the lower node count is consistent with contention, not
a regression — nothing in this session's changes (the daemon fix, or the 4
earlier CSS fixes) touches this code path, and the reasoning above rules out
any code-sharing explanation.

**Conclusion: confirmed unchanged.** The daemon debug-seed-shadowing fix does
not intersect this code path at all — different spawn logic, verified both by
source and by live `ps`/`/proc/exe` inspection — and was never expected to.
U2 remains blocked on the same, already-understood, already-out-of-scope
interpreted-lane HIR-lowering defect. No sabotage test performed (no green
baseline exists to sabotage). This is a legitimate, expected "nothing changed"
result, not a stale or skipped re-check.
