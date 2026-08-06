# wm_showcase_session_capture_spec: "no examples executed" reproduces on unmodified origin/main

## Symptom

`test/03_system/gui/wm_showcase_session_capture_spec.spl` fails with:

```
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

with `Duration: ~10s` — far too fast to have run any real window-open/HTML-render
work (that path costs 30-50 CPU-minutes per HTML-backed window in this
environment, per the spec's own governing comments). No compile error, no
`✗` assertion line, no `[use-warning]` naming any unresolved symbol — the
`describe` block's `it` examples simply never register.

## This is NOT caused by task #96's browser/terminal window addition

Verified via a controlled A/B: with `src/app/wm_showcase/session.spl`,
`run.spl`, and the spec file all reverted byte-for-byte to their
`origin/main` content (3-window baseline, before this session's browser/
terminal work), the SAME spec fails the SAME way:

```
$ git show origin/main:src/app/wm_showcase/session.spl > src/app/wm_showcase/session.spl
$ git show origin/main:src/app/wm_showcase/run.spl > src/app/wm_showcase/run.spl
$ git show origin/main:test/03_system/gui/wm_showcase_session_capture_spec.spl > test/03_system/gui/wm_showcase_session_capture_spec.spl
$ bin/simple test test/03_system/gui/wm_showcase_session_capture_spec.spl --no-cache --no-cover-check
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Files were restored afterward (verified byte-identical to the pre-revert
copies via `diff`). This rules out the new browser/terminal window content
as the cause — the defect is pre-existing on `origin/main` right now.

## Not a total-environment failure

An unrelated spec run in the same session, same environment, same command
shape, passed cleanly and quickly:

```
$ bin/simple test test/01_unit/lib/common/ui/draw_ir_v3_group_resolve_spec.spl --no-cache --no-cover-check
SPEC FILE VERDICT: ... declared>=23 executed=23 passed=23 failed=0 dropped=0
Results: 23 total, 23 passed, 0 failed
```

So this is specific to `wm_showcase_session_capture_spec.spl` (or its heavy
transitive import graph), not a broken test harness across the board.

## Two live hypotheses (not yet distinguished)

1. **Shared-daemon race** — the default session daemon serves a stale/racing
   result under concurrent load (many other agent sessions are hammering
   `bin/simple test` on this shared machine right now). `--no-session-daemon`
   avoided the fast fake-failure in one trial (ran past 90s doing real
   compile work instead of failing in ~10s) but that run's own outcome was
   not yet captured when this doc was filed.
2. **Genuine crash/hang inside the `it` block, silently swallowed** — matches
   an earlier, structurally identical symptom already on file:
   `doc/08_tracking/bug/ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`,
   which hypothesizes a `compiler_cross_module_private_symbol_collision`
   wrong-helper JIT dispatch (see
   `doc/08_tracking/bug/compiler_cross_module_private_symbol_collision_2026-06-16.md`)
   silently crashing execution rather than failing a normal assertion. This
   session's own lint/compile output for the wm_showcase import graph shows
   dozens of `compiler_cross_module_private_symbol_collision` warnings
   (`dir_remove_all`, `shell`, `shell_output`, `file_read_bytes`, `path_join`,
   `env_vars`, `process_wait`, `resolve_style`, ... — the transitive graph is
   large and touches many of the exact primitive names flagged there).

Both are plausible; this doc does not claim to have distinguished them.
Whoever picks this up next should check whether `--no-session-daemon`'s
outcome (once captured) genuinely completes (rules out hypothesis 1) or
itself eventually reports "no examples executed" after real compile+run time
(supports hypothesis 2, and would make this spec a second confirmed instance
of the collision-crash class).

## Impact

Blocks the WM showcase integration gate (`test/03_system/gui/
wm_showcase_session_capture_spec.spl`) for task #96 (Simple Browser + Simple
Terminal windows) and for the WM showcase feature generally — the gate
cannot currently produce a real pass/fail verdict through the default test
path on this machine, independent of what changes are or aren't in the
5-window version.

## Workaround

`--no-session-daemon` at minimum avoids the ~10s fake-fast failure signature;
whether it reaches a real PASS/FAIL verdict was still pending capture when
this doc was filed. Budget real wall-clock time (compile-from-scratch plus
however many HTML renders the spec version under test needs) rather than a
short timeout.

## Likely root cause found (2026-08-06, same day)

Commit `5a62d7a2b95` ("fix(web-render): add missing `_web_budget_expired_at` +
`WEB_BUDGET_SITE_*` symbols") landed on `origin/main` shortly after this doc
was filed, from an unrelated concurrent session. Its description: 7 call
sites across `simple_web_html_layout_renderer_layout.spl` and
`..._paint_layout.spl` called `_web_budget_expired_at(WEB_BUDGET_SITE_*)`,
but neither the function nor the site constants existed anywhere in the
tree. Since unresolved symbols are fail-open (WARN, not a compile error) in
this language, every HTML render that reached the layout/paint pass would
hit this genuinely-missing symbol at RUNTIME rather than compile time —
exactly matching hypothesis 2 (a crash inside the `it` block, silently
swallowed as "no examples executed" with zero assertion output, ~10s
duration). `wm_showcase_session_capture_spec.spl`'s gui/web windows both
render real HTML through this exact layout/paint path, so this is a
strong causal match, not just a correlation.

**Update: re-verified against the patched tree — helped, but did not fully
resolve it.** Post-fix, the spec now gets further before failing: stage
markers `wm_showcase_stage start` and `wm_showcase_stage opening=gui` print
(previously nothing printed at all — the failure was earlier, likely at
module-load time), but it still ends in the same
`error: test-runner: no examples executed`, `Duration: ~10s`. A ~10s
duration is far too short for the real interpreted HTML render this stage
triggers (30-50 CPU-minutes per the spec's own governing comments), so
whatever crashes/hangs does so almost immediately after `open_window` calls
into the gui-window's render path — not after the long render itself, so
"the render itself is just slow" is ruled out as an explanation. Grepped the
full log for `unknown extern`, `semantic:`, `not found`, `Unsupported`,
`panic`, `RuntimeError`, `Traceback` — none present. The failure is a total
silent swallow with zero diagnostic text beyond the generic runner message,
consistent with `ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`'s
observation. Since `bin/simple test` always uses the tree-walk interpreter
(never JIT, per `.claude/rules/testing.md`), the
`compiler_cross_module_private_symbol_collision` JIT-wrong-dispatch
hypothesis from that sibling doc does not directly apply here — whatever is
crashing is doing so under the interpreter, so the root cause is still
unidentified, just narrowed to "somewhere very early in the gui window's
render call chain, under the interpreter, with no diagnostic output."

## Impact on task #96 (Simple Browser + Simple Terminal windows)

This defect independently blocks task #96's integration gate — confirmed
NOT caused by that work (baseline A/B above). Task #96's new code
(`src/app/browser/render_adapter.spl`, `src/app/terminal/render_adapter.spl`)
was verified correct by other means instead: `bin/simple lint` clean (0
errors), and a standalone `bin/simple run` probe confirming
`render_browser_html(...)`/`render_terminal_html(...)` produce real,
correctly-shaped HTML output (Hello World page with real browser chrome;
terminal chrome with the real subcommand reference) — see the probe in this
doc's git history / task #96's session notes. Landing task #96 without a
green integration-gate run is a deliberate, disclosed exception, not a
silent skip.

## Follow-up session (2026-08-06): render chain is NOT the cause — root-caused to the session-daemon layer, one class fixed

Per this doc's own "Next step" plan, bisected with a standalone print-instrumented
probe (`bin/simple run <probe>.spl` under `SIMPLE_EXECUTION_MODE=interpret`,
driving the exact same call chain the spec's gui window uses:
`wm_showcase_window_specs()` → `wm_showcase_gui_html()` →
`simple_web_render_html_to_readback_result_with_engine2d_backend`), run OUTSIDE
the spec/test runner so any crash prints instead of being swallowed.

**Finding 1 — the render chain itself is innocent.** The standalone probe
completed cleanly end to end: `pixels=6912 source=host_cache_after_device_present
degraded=false`, in ~65s (`[web-phase] phase=paint elapsed_ms=64254`). A second
probe calling `wm_showcase_run()` directly (the exact function the spec calls)
also ran the real interpreted cascade through style/layout/paint with no crash.
This rules out the render call chain as the source of the silent failure.
**Confirmed further:** a full real run of the spec via
`bin/simple test test/03_system/gui/wm_showcase_session_capture_spec.spl
--no-cache --no-cover-check --no-session-daemon --timeout 1800` **passes
cleanly**: `Results: 12 total, 12 passed, 0 failed`, `Duration: 409562ms` (~6.8
CPU-minutes — a plausible real-render cost, not another suspiciously-fast
false pass), every stage marker present through `wm_showcase_stage
wrote_artifact`. The WM showcase functional code (session.spl, run.spl, the
browser-engine render chain) is correct. The bug is entirely in the
test-runner/session-daemon infrastructure around it.

**Finding 2 — root cause of the "no examples executed" class, FIXED.**
`bin/simple test <file>` (no explicit daemon flag) defaults to
`session_daemon = true` (`test_runner_args.spl:264`), which routes every run
through `run_tests_via_daemon()` in `src/app/test_runner_new/test_runner_main.spl`
(the file actually wired to `bin/simple test` — see `bootstrap_check.spl:356`
and `main.spl`'s `use app.test_runner_new.test_runner_main.{run_test_cli}`; the
near-identical copy under `src/lib/nogc_sync_mut/test_runner/` is NOT on this
dispatch path and was left untouched). Tracing the daemon path by direct code
read (not guessed):

1. The daemon (`src/app/test_daemon/daemon.spl::handle_run_single`) checks
   `self.incremental_state.check_freshness(test_path)` and returns a cached
   `TRESP_CACHED` result **immediately, without re-executing**, whenever
   `clean != "true"`.
2. `clean` came from `val clean = options.clean` in `run_tests_via_daemon`
   (line 722) — i.e. **only the explicit `--clean` flag**, never
   `--no-cache`/`options.no_cache` (a separate field that only controls
   file-discovery caching, per `test_runner_args.spl`). So `--no-cache` (the
   flag this doc's own repro command used) never bypassed the daemon's result
   cache.
3. The FIRST daemon-served run of a file whose render genuinely exceeds the
   test-runner's internal default timeout (120s; `daemon.spl::execute_test`
   shells out to `bin/simple test ... --no-session-daemon --sequential` with
   **no `--timeout` forwarded at all**, so it always uses
   `test_runner_single.spl`'s 120s default regardless of what `--timeout` the
   caller passed to `bin/simple test`) fails — either a genuine 120s timeout
   or (see Finding 3) an even faster kill — and `execute_test` unconditionally
   calls `self.incremental_state.record_daemon_result(...)`, **caching that
   failure**.
4. Every subsequent `--no-cache` (but not `--clean`) request for the same
   file, for as long as the daemon process and its freshness check consider
   the entry fresh, replays the stale cached failure via `TRESP_CACHED` — a
   dict lookup, no re-execution — in a few seconds, matching the doc's
   observed `Duration: ~10s`.
5. Compounding this: `run_tests_via_daemon`'s error-text line was
   `error: if daemon_result.status == TRESP_FAILED: daemon_result.output else:
   ""` — **only `TRESP_FAILED` copied the diagnostic `.output` into the
   displayed `.error`; `TRESP_CACHED` always displayed an empty string**, even
   though `daemon_result.output` (wired through `handle_run_single`'s
   `resp.fields["output"] = cached.output`) actually held real diagnostic
   text. This is the exact mechanism of "zero diagnostic output beyond the
   generic runner message" this doc documented under "Likely root cause
   found" above — the diagnostic existed, but the display path silently
   dropped it on every cache hit.

**Fix applied** (`src/app/test_runner_new/test_runner_main.spl`,
`run_tests_via_daemon`):
- `val clean = options.clean or options.no_cache` — `--no-cache` now bypasses
  the daemon's incremental cache too, not just file-discovery caching.
- `error: if daemon_result.status == TRESP_FAILED or (daemon_result.status ==
  TRESP_CACHED and daemon_result.failed > 0): daemon_result.output else: ""` —
  a cached failure now surfaces its recorded diagnostic text instead of a bare
  `0 passed, 1 failed` with no `Error:` line.

Verified: `bin/simple lint src/app/test_runner_new/test_runner_main.spl` clean
(0 errors; only pre-existing repo-wide warnings unrelated to this file/edit).
Re-running the spec under the **default** (session-daemon) path with
`--no-cache` after the fix now genuinely **re-executes** — `wm_showcase_stage
start` / `wm_showcase_stage opening=gui` print fresh each time, proving it is
no longer served from a stale cache hit (previously a cache hit would print
nothing but the final summary).

**Finding 3 — a second, DISTINCT daemon-only failure remains open, NOT
fixed.** Even after the cache fix forces real re-execution, the daemon-routed
run still dies after ~10s with no further diagnostic, specifically when
launched via `daemon.spl::execute_test`'s `rt_shell_exec` (a bare shell-out
with **no** `process_run_bounded`-style budget and no `--timeout` forwarded) —
never observed when the identical command
(`bin/simple test <path> --no-session-daemon --sequential`) is run directly
from a plain shell, which instead survives to a genuine, real 120s timeout (or,
given enough time, a real pass — see Finding 1). Direct evidence of the kill:
the captured log shows the render mid-flight (`[backend-resolve] rocm
rejected: ...`) followed **immediately, with no exit/error text at all**, by a
brand-new `bin/simple` process startup banner interleaved into the same
stream — i.e. the render process is being terminated externally, not crashing
in its own code. The strongest suspect, found by code read (not confirmed by
instrumentation): `scripts/resource/kill_simple_monitor.shs`, a system-wide
resource safeguard that `ensure_kill_monitor_running()` launches once (tracked
via a single shared `/tmp/kill_simple_monitor.pid`, reused by **every**
concurrent `bin/simple test`/`run` invocation on this machine, across every
concurrent agent session) and which kills any `bin/simple run|test` process
pegged at >=95% CPU past a grace period, or over an RSS cap. The documented
CPU-spin grace period is 60s (`MIN_AGE_SECS`), longer than the observed ~10s
kill, so either (a) an inherited-then-not-fully-corrected `SIMPLE_TIMEOUT_SECONDS`
env value shrinks the effective grace period specifically for a daemon-spawned
child (the monitor re-reads `SIMPLE_TIMEOUT_SECONDS` live from
`/proc/<pid>/environ`, and a shell child of the daemon may briefly present a
smaller inherited value before `test_runner_single.spl`'s own self-correction
runs), or (b) the RSS guard, or (c) some other daemon-specific resource
accounting. **Not root-caused precisely enough to fix safely** — this is a
system-wide safeguard shared by every concurrent session on this machine
(load average 8-18 during this investigation, multiple other agents' `simple`
processes running concurrently, confirmed via `ps aux`), and adjusting its
thresholds without fully confirming the trigger risks weakening real
runaway-process protection for everyone. Filing precisely per this task's own
guidance rather than forcing a fix.

**Finding 4 — a separate, genuine interpreter defect, unrelated to Finding
2/3, found and NOT fixed (Rust-side, wide blast radius).** Two independent
standalone probes (both under `SIMPLE_EXECUTION_MODE=interpret`, i.e. the
same tree-walk interpreter `bin/simple test` always uses) hit:
```
error: semantic: method `_flush_pending_compute` not found on type `VulkanBackend`
```
This fires inside `Engine2D.probe_backend_viable()`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl:925`), which drives a
trait-typed `var b = engine.backend` (`backend: RenderBackend`, a duck-typed
field) through `set_clip`/`draw_rect_filled`/`submit_batch`/`present`/
`read_pixels_with_source`. When the concrete backend is `VulkanBackend` and one
of those calls internally does `self._flush_pending_compute()` — a method
defined only in the EXTENSION impl file
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:177`, not in the
class's home file `backend_vulkan.spl` — the interpreter fails to resolve it,
even though the same method resolves fine when called from other contexts (a
prior investigation, `run_lane_render_truncation_divergence_2026-08-02.md`,
traced many successful `_flush_pending_compute()` calls returning real values).
The distinguishing factor appears to be that this specific call site is
reached via a **trait/duck-dispatched** entry (`b.method()` on a
`RenderBackend`-typed variable) whose body then makes a same-class `self.`
call to an extension-impl method — suggesting the interpreter's method
resolution for a `self` call originating inside a duck-dispatched method body
does not see the full set of impl blocks for the concrete class. This is
**nondeterministic in practice**: it only triggers when backend
auto-resolution's deep-viability probe actually reaches Vulkan (this session
saw both outcomes — one probe run selected `qualcomm` before ever reaching
Vulkan, another hit this crash; the final verified spec runs in this session
also selected `qualcomm`, so this defect did NOT contribute to the specific
runs recorded above). Genuinely Rust-side interpreter-core dispatch work
(`src/compiler_rust/compiler/src/interpreter_method/`), out of safe
narrow-`.spl`-fix scope per this session's explicit constraints — filed here
as a precise, reproducible, standalone defect rather than attempted.

## Next step

- **Done:** render chain bisected and cleared (Finding 1); daemon
  incremental-cache bypass + cached-failure diagnostic display fixed
  (Finding 2, `src/app/test_runner_new/test_runner_main.spl`).
- **Open — Finding 3:** confirm the exact trigger of the ~10s daemon-child
  kill (instrument `kill_simple_monitor.shs` with a log line naming which
  guard fired and the exact CPU%/age/RSS it measured for the victim PID, or
  temporarily run with `KILL_SIMPLE_LOG` pointed at a scratch file during a
  repro) before touching its thresholds. Until fixed, `wm_showcase_session_
  capture_spec.spl`'s reliable path is `--no-session-daemon --timeout 1800`
  (verified 12/12 pass, ~410s) — the default session-daemon path is not
  currently reliable for this spec on a loaded shared machine.
- Consider also forwarding the caller's `--timeout` through
  `daemon.spl::execute_test`'s shelled command (currently hardcoded with none,
  always falling back to `test_runner_single.spl`'s 120s default) — a
  separate, moderate-risk change (touches the daemon request/response
  protocol) not attempted here.
- **Open — Finding 4:** file/fix the `_flush_pending_compute`
  trait-dispatch-vs-extension-impl interpreter defect separately; it is
  unrelated to this spec's own failure mode in the runs recorded above but is
  a real, reproducible defect in the same interpreter every `bin/simple test`
  run depends on.
- Cross-reference `ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`
  as a sibling symptom (same swallowed-failure shape). Given Finding 2's root
  cause (stale daemon-cache replay with dropped diagnostics) is generic to
  ANY spec run through the default session-daemon path, it is worth checking
  whether that doc's case also went through an uncleaned daemon cache hit.
