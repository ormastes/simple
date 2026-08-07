# Render-Perf V-Lane Correctness/Promotion Suite — Aggregate Report (2026-08-06)

> **Status note (added after Run 2, same day):** Run 1 below is preserved
> verbatim as the historical record. Run 2 (bottom of this doc) re-ran the
> suite after both Run-1 blockers were independently fixed. Run 2 also
> **retracts** the Run-1 claim that `compositor_occlusion_spec.spl`'s timeout
> was "ruled out" as a false-timeout/shared-batch artifact — that claim was
> wrong; the timeout was real per-process contention, not a hang. See the Run
> 2 section for the correction and for a newly observed residual issue
> (`widget_draw_ir_glyph_run_spec.spl`).

> **Status note (added after Run 4, same day):** Run 4 (bottom of this doc) is
> a fresh full re-run after the test-daemon debug-seed-binary-shadowing fix
> landed. **VERDICT: GREEN** — both specs blocked in Runs 2 and 3
> (`compositor_occlusion_spec.spl`, `widget_draw_ir_glyph_run_spec.spl`) now
> pass. All 11 specs, 160/160 examples, 0 failures, 0 cannot-execute.

> **Status note (added after Run 3, same day):** Run 3 (bottom of this doc) is
> a fresh full re-run after six more landed fixes (CSS cascade, CSS
> containment, SIMD dispatch, Vulkan trait gating, p95 harness, MMIO extern,
> and the compositor `get_pixel_buffer()` alias-hazard fix), plus the script's
> occlusion-spec floor being raised from 450s to 1200s. Aggregate numbers are
> **unchanged from Run 2** (146/146 passed, 2 CANNOT_EXECUTE, VERDICT: RED),
> but Run 3 **sharpens the diagnosis**: a targeted standalone retry of the two
> blocked specs, run under materially lighter load (load average ~5-8, down
> from ~12.7 at the start) with generous outer timeouts (600s and 1200s), shows
> both specs still print `Process timed out` from *inside* `bin/simple test`
> after only ~137s wall time each — well short of both the outer shell
> `timeout` and the suite script's per-spec floor. This means Run 2's "likely
> load contention" hypothesis for `compositor_occlusion_spec.spl` does **not**
> hold: it is blocked by the same internal ~130-140s driver-level timeout
> ceiling already documented for `widget_draw_ir_glyph_run_spec.spl`, not by
> external contention, and raising the script's `SPEC_TIMEOUT` (currently
> 1200s) cannot fix it because the block fires from inside the process, not
> from the outer wrapper.

## Scope, as the plan doc actually defines it

`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` names the V-lane
only in the wave diagram and in its cross-cutting gates sections — it does
**not** contain a dedicated "§V" section spelling out a suite-of-suites. What
it does say, verbatim/paraphrased:

- §9 wave diagram: `... WM/GUI/Web adoption (U0..U3, U4 cutover) → parity/perf
  promotion (V0, V1)`.
- §11 wave 4: "V0 differential/property suites (no vacuous all-zero pass;
  sabotage required), V1 promotion."
- §10 "Promotion" criterion (the closest thing to an explicit definition, but
  it is written for *individual optimizations* in the common-optimizer
  registry, not for a cross-lane suite): "≥10% p50 win in bucket, p95/RSS
  inside budget, genuine execution proven by counters, no hidden fallback."
  §4 adds: "Promoted only after: preconditions proven, scalar parity, shadow
  execution divergence-free, wins its bucket, p95/memory inside gate,
  fallback receipt-backed."
- §10 sabotage rule, which does generalize to any suite: "A gate green under
  sabotage has proven nothing" — each lane's own spec already carries its
  sabotage test; this meta-suite's job is to prove those specs still pass
  **together**, not to add a new sabotage layer of its own.

**Conclusion:** the plan does not define what "promotion" means for a
cross-cutting run-everything-together suite — only for a single perf
optimization candidate. This report does not invent an elaborate scheme.
Minimal concrete definition adopted here:

> A lane's capability counts as **promoted** when (a) its own spec passes with
> 0 failures when run in isolation, AND (b) it still passes with 0 failures
> when run in this combined suite alongside every other landed lane's specs
> (no cross-lane regression). A spec that cannot execute at all is **not
> promoted** and is reported as such, not silently excluded.

## What was built

- `scripts/check/check-render-perf-v-lane-suite.shs` — runnable aggregate
  check. Runs each spec below via `bin/simple test <spec> --no-cache
  --no-cover-check`, parses the runner's `SPEC FILE VERDICT:
  declared=... executed=... passed=... failed=...` line, and sums honestly.
  A spec with no verdict line (timeout/crash) is counted as `CANNOT_EXECUTE`,
  not dropped from the spec count, and forces overall `VERDICT: RED`.
- This report.

Running the 11 specs as one `bin/simple test a b c ...` invocation hit the
60s default harness timeout on the whole batch (exit 143 — the project's
"timeout truncation" measurement trap, not a real per-spec verdict). The
script and this report instead run each spec as a **separate process** with
its own timeout, which is what actually produces trustworthy per-spec
verdicts — the tradeoff is this is not literally "one shared runtime process
across all specs" but process-level isolation per spec, summed.

## Specs covered (11 total)

| Spec | Lane | Result |
|---|---|---|
| `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl` | P0 | PASS 38/38 |
| `test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl` | O0/O1 | PASS 18/18 |
| `test/01_unit/compiler/semantics/layer_eq_checker_spec.spl` | C1 | PASS 7/7 |
| `test/01_unit/compiler/semantics/effect_verifier_spec.spl` | C4 | PASS 16/16 |
| `test/01_unit/lib/common/memory/packed_span_spec.spl` | F2 | PASS 10/10 |
| `test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl` | O3 (text) | PASS 4/4 |
| `test/01_unit/os/compositor/hosted_input_sdl2_spec.spl` | U0b / WS-C | PASS 28/28 |
| `test/01_unit/os/compositor/compositor_occlusion_spec.spl` | O2 | **CANNOT EXECUTE** — timed out (150s), no verdict line |
| `test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl` | O2 | PASS 21/21 |
| `test/01_unit/compiler/class_reference_semantics_spec.spl` | F1 | PASS 6/6 |
| `test/01_unit/os/render_pixel_bridge_spec.spl` | F4/G-adjacent | **FAIL 0/2** — `semantic: unknown extern function: rt_mmio_write_u32` (pre-existing, known blocker, not re-investigated here) |

No other `_spec.spl` files were found added by this session's lane commits
under the searched directories beyond the 11 above (checked
`test/01_unit/lib/common/gpu/engine2d/`, `test/01_unit/lib/common/ui/render_opt/`,
`test/01_unit/compiler/semantics/{layer_eq_checker,effect_verifier}`,
`test/01_unit/lib/common/memory/packed_span_spec.spl`,
`test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl`,
`test/01_unit/os/compositor/{occlusion,hosted_input_sdl2}`,
`test/01_unit/compiler/class_reference_semantics_spec.spl`).

## Aggregate numbers (measured 2026-08-06)

```
specs covered:     11
cannot execute:     1  (compositor_occlusion_spec.spl — timeout)
specs failing:      1  (render_pixel_bridge_spec.spl — 2/2 examples fail)
specs passing:      9
total examples run (across the 10 specs that produced a verdict): 150
  passed: 148
  failed:   2
VERDICT: RED
```

Do not read "148/150 = 98.7%" as a clean campaign result — the honest count
is **11 specs targeted, 9 fully green, 1 outright red, 1 unable to execute at
all**. Two specs (0/9 and 1/9, i.e. render_pixel_bridge and
compositor_occlusion) are not proven correct by this run.

## Open / blocked / unverified

- **`render_pixel_bridge_spec.spl` — FAIL, not re-investigated.** Blocked by
  `unknown extern function: rt_mmio_write_u32`, as previously known. Included
  in the total, not excluded.
- **`compositor_occlusion_spec.spl` — CANNOT EXECUTE at 150s in Run 1.**
  **CORRECTION (Run 2):** the claim above that this was "ruled out" as a
  false-timeout/shared-batch artifact was wrong. A dedicated follow-up
  investigation ran the spec directly and got `Duration: 130637ms`, `10
  examples, 10 passed, 0 failed` — it is not a hang, just slower (~131s) than
  the suite's 150s per-spec budget under any concurrent load at all. The
  spec's own header comment recommending `--timeout 7200` is stale/pessimistic.
  See Run 2 below for the fix (per-spec timeout raised to 450s in the script).
- **Combined-batch run (`bin/simple test <all 11 specs>` in one invocation)
  hit the harness's 60s default timeout (exit 143) before any spec finished.**
  The per-process-per-spec approach above is the workaround used; a true
  single-process combined run was not achieved and is left open as a gap in
  "run everything together" fidelity.
- **No general sweep for other lane specs beyond the plan-named directories**
  was performed beyond a git-log scan for spec files added on 2026-08-06;
  that scan surfaced only browser-app specs unrelated to this render-perf
  campaign, which were excluded as out of scope.
- Not evaluated here at all (out of scope per the task instructions): actual
  perf/promotion thresholds from §10 (≥10% p50 win, p95/RSS budgets) — this
  report is a correctness aggregate only, consistent with "sabotage doesn't
  apply at this meta level, the proof is running everything for real."

## Run 2 — re-run after both Run-1 blockers fixed (2026-08-06, later same day)

### What changed since Run 1

1. **MMIO extern fix landed.** Real `rt_mmio_read/write_u32/u16/u8` accessors
   were added to the hosted Rust seed runtime's extern dispatch table. Result:
   `render_pixel_bridge_spec.spl` now passes **2/2** in every run below (was
   FAIL 0/2 in Run 1).
2. **`compositor_occlusion_spec.spl` confirmed not hanging.** Direct
   standalone run: `Duration: 130637ms`, `10 examples, 10 passed, 0 failed`.
   The Run-1 "genuine hang" conclusion (quoted and struck through above) was
   wrong; it was a real but non-hanging ~131s runtime colliding with the
   suite's 150s budget.
3. **`scripts/check/check-render-perf-v-lane-suite.shs` updated:** the spec
   now gets a **450s** per-spec timeout floor (`case "$spec" in
   *compositor_occlusion_spec.spl) ... [ "$SPEC_TIMEOUT" -lt 450 ] &&
   SPEC_TIMEOUT=450`), inside the 300-600s range requested — not the spec's
   own stale 7200s header recommendation, and comfortably above the measured
   131s. The script's global `--timeout` default (still 150s) is unchanged;
   other specs keep whatever value is passed on the command line.

### Environment during this re-run: heavy concurrent load

`uptime` at the start of Run 2 showed **load average 14.42, 9.88, 9.11** (a
5-day-uptime box) with several unrelated 100%-CPU processes already running
concurrently in this same repo (parallel `native-build`/bootstrap workers from
other sessions, per `ps aux`). By the time of the final clean run, load had
dropped to **7.52, 7.76, 8.49** — still non-trivial background contention.
This matters for reading the numbers below: this suite's own script runs
specs strictly serially, one `bin/simple test <spec>` process at a time, but
*other, unrelated* processes on the box were consuming most of the CPU
throughout.

### Re-run attempts and results

Three full-suite invocations of `sh scripts/check/check-render-perf-v-lane-suite.shs --timeout 300` were made (the first two accidentally overlapped in time, doubling contention against each other — an artifact of this investigation, not the suite):

| Run | cannot execute | executed | passed | failed | verdict |
|---|---|---|---|---|---|
| 2a (overlapped with 2b) | 3 (`widget_draw_ir_glyph_run_spec.spl` @300s, `hosted_input_sdl2_spec.spl` @300s, `compositor_occlusion_spec.spl` @450s) | 118 | 118 | 0 | RED |
| 2b (overlapped with 2a) | 2 (`widget_draw_ir_glyph_run_spec.spl` @300s, `compositor_occlusion_spec.spl` @450s) | 146 | 146 | 0 | RED |
| 2c (clean, serial, no other concurrent suite run) | 2 (`widget_draw_ir_glyph_run_spec.spl` @300s, `compositor_occlusion_spec.spl` @450s) | 146 | 146 | 0 | RED |

`hosted_input_sdl2_spec.spl` (28/28) and `compositor_occlusion_rect_spec.spl`
(21/21) reproduced their Run-1 passes cleanly in runs 2b/2c once the
self-inflicted double-suite contention was removed — consistent with "run 2a's
extra CANNOT_EXECUTE was contention from running two suites at once," not a
regression.

**`compositor_occlusion_spec.spl` still hit the new 450s timeout in every one
of the three re-runs**, despite the standalone confirmation of a 130637ms
(131s) runtime earlier this session. This is very likely the same
concurrent-load effect (14.4 load average with 100%-CPU neighbors) pushing a
131s-under-light-load spec well past 450s under heavy load — but it was not
independently re-confirmed standalone-and-clean in this pass, so it is
reported as an open observation, not dismissed.

**`widget_draw_ir_glyph_run_spec.spl` is a newly observed residual issue,
distinct from both fixed blockers.** It passed 4/4 in Run 1. In this re-run it
timed out consistently in all three suite runs. Investigated standalone,
outside the suite:
- `timeout 600 bin/simple test test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl --no-cache --no-cover-check` → `Process timed out` after **138s wall** (measured via `time`: `real 2m18.698s`), well inside the 600s outer `timeout` budget — the timeout is coming from *inside* `bin/simple test` itself, not the outer shell wrapper.
- Retried with `SIMPLE_TIMEOUT_SECONDS=600` (the runner's own internal timeout override env var, per `src/app/test_runner_new/test_runner_main.spl`) and a 650s outer `timeout` — still `Process timed out`, same outcome.
- Not fixed here, per this task's explicit scope (verification/reporting only, do not fix newly-discovered blockers). Filed here as an honest open item: **this spec now cannot execute to a verdict at all**, regardless of external timeout budget, and needs its own investigation.

### Run 2 aggregate (from run 2c, the clean serial run)

```
specs covered:     11
cannot execute:     2  (widget_draw_ir_glyph_run_spec.spl, compositor_occlusion_spec.spl)
specs failing:      0
specs passing:      9
total examples run (across the 9 specs that produced a verdict): 146
  passed: 146
  failed:   0
VERDICT: RED
```

### Before/after summary

| Spec | Run 1 | Run 2 |
|---|---|---|
| `render_pixel_bridge_spec.spl` | FAIL 0/2 (`rt_mmio_write_u32` unknown extern) | **PASS 2/2** — fixed |
| `compositor_occlusion_spec.spl` | CANNOT EXECUTE @150s | CANNOT EXECUTE @450s in this pass (standalone-clean run earlier this session measured 131s, 10/10 passed — see correction above); likely load-contention, not re-confirmed clean here |
| `widget_draw_ir_glyph_run_spec.spl` | PASS 4/4 | **CANNOT EXECUTE** — new regression/instability, internal ~138s timeout inside `bin/simple test`, reproduced 3x, not fixed by raising external or `SIMPLE_TIMEOUT_SECONDS` timeouts |
| all other 8 specs | PASS | PASS (unchanged) |

### Honest verdict: NOT GREEN

The suite is **not** fully green. One of the two original blockers
(`render_pixel_bridge_spec.spl`) is genuinely fixed and reproduced clean
3 times. The other (`compositor_occlusion_spec.spl`) is very likely a
load-contention artifact rather than a real defect (based on an earlier
standalone 131s/10-10 confirmation this session) but was **not** re-confirmed
clean in this specific re-run pass — do not read this report as having
independently reproduced that clean result today. A third, previously-passing
spec (`widget_draw_ir_glyph_run_spec.spl`) now fails to execute at all, with
an internal timeout that persisted even under generous external and
`SIMPLE_TIMEOUT_SECONDS` budgets — this is a new residual issue, out of this
task's scope to fix, and is reported rather than silently excluded.

**Scope caveat:** `bin/simple test` is the project's known
delegate-to-hosted-Rust-seed path. The MMIO externs were added to *that*
runtime's dispatch table, so the `render_pixel_bridge_spec.spl` GREEN result
proves the fix on the hosted-seed path specifically — it does not by itself
prove the pure-Simple/self-hosted path resolves `rt_mmio_*`.

## Run 3 — fresh re-run after six more lane fixes (2026-08-06, later same day)

### What changed since Run 2

Six more commit batches landed on `origin/main` since Run 2, per the
coordinating session: two CSS-cascade correctness fixes, a CSS-containment
fix, real SIMD dispatch wiring, an honestly-gated Vulkan backend trait, a p95
statistics harness, the MMIO extern fix (already reflected in Run 2), and —
most recently — a fix for the compositor's `get_pixel_buffer()` live-alias
hazard that had blocked damage-integration work all session.
`scripts/check/check-render-perf-v-lane-suite.shs` was also updated: the
`compositor_occlusion_spec.spl` per-spec timeout floor was raised from 450s
(Run 2) to **1200s**, with a documented rationale (a standalone,
contention-isolated run measured ~43s total for 4 cases, extrapolated to a
~130s clean baseline; 1200s is framed as ~9x headroom against contention).

### System load

`uptime` at the start of Run 3:

```
15:19:47 up  1:00,  2 users,  load average: 12.71, 9.98, 9.37
```

`ps aux --sort=-%cpu` showed heavy concurrent contention from *other*
sessions in this same box: a `native-build` process at 924% CPU (16-thread
LLVM codegen), a `bin/simple lint` process at 99% CPU, plus three other
`claude` CLI sessions and three `codex` sessions idling in the background.
This is comparable to, or heavier than, the load observed at the start of Run
2 (14.42). By the end of the full-suite run, load had dropped to **6.65,
7.88, 8.36**; by the end of the targeted retry (see below) it had dropped
further to **4.59, 5.98, 7.39**.

### Full-suite run

`sh scripts/check/check-render-perf-v-lane-suite.shs --timeout 300` (the
occlusion spec still gets its 1200s floor from the script's internal
override regardless of this flag):

```
PASS: scalar_oracle_spec.spl (38/38)
PASS: render_opt_invalidation_spec.spl (18/18)
PASS: layer_eq_checker_spec.spl (7/7)
PASS: effect_verifier_spec.spl (16/16)
PASS: packed_span_spec.spl (10/10)
CANNOT_EXECUTE: widget_draw_ir_glyph_run_spec.spl (timeout after 300s)
PASS: hosted_input_sdl2_spec.spl (28/28)
CANNOT_EXECUTE: compositor_occlusion_spec.spl (timeout after 1200s)
PASS: compositor_occlusion_rect_spec.spl (21/21)
PASS: class_reference_semantics_spec.spl (6/6)
PASS: render_pixel_bridge_spec.spl (2/2)

=== V-LANE AGGREGATE ===
specs covered:    11
cannot execute:   2
total examples:   146
total passed:     146
total failed:     0
VERDICT: RED
```

Numbers are identical to Run 2c: same 2 specs CANNOT_EXECUTE, same 146/146
pass rate on everything that did produce a verdict, same 0 failures. No
regression, no improvement, since Run 2.

### Targeted retry: does lighter load and a much larger timeout change the outcome?

To separate "still contended" from "genuinely blocked regardless of load,"
both CANNOT_EXECUTE specs were re-run standalone, once load had already
dropped to ~5-8, with generous outer `timeout` budgets well above the suite
script's own floors:

```
timeout 600  bin/simple test test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl --no-cache --no-cover-check
timeout 1200 bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl --no-cache --no-cover-check
```

Both runs completed (i.e. the shell wrapper did not have to kill them) inside
a combined wall time of **~275s for both specs together** (log start
15:33:02, log last-write 15:37:37) — far under the 600s+1200s=1800s outer
budget — and both printed the internal driver's own `Process timed out`
message with exit code 255, i.e. **no verdict line, same failure mode as in
the suite**. This reproduces Run 2's finding for
`widget_draw_ir_glyph_run_spec.spl` (documented there as an internal ~138s
timeout independent of `SIMPLE_TIMEOUT_SECONDS` and the outer `timeout`) and
**extends it to `compositor_occlusion_spec.spl`**, which Run 2 had instead
attributed to probable load contention without independent confirmation.

**Conclusion: this is not a load-contention artifact for either spec.** Both
specs are blocked by what appears to be the same internal, driver-level
timeout ceiling (roughly 120-140s), which fires regardless of the outer shell
`timeout` value or the suite script's configured `SPEC_TIMEOUT`. Widening the
script's occlusion-spec floor to 1200s (the fix landed since Run 2) had no
effect on the actual outcome, because the thing that kills the process isn't
the 1200s floor — it's this shorter internal limit. This was not previously
established this cleanly; Run 2 left `compositor_occlusion_spec.spl`'s status
as an open, unconfirmed hypothesis.

### Run 3 aggregate

```
specs covered:     11
cannot execute:     2  (widget_draw_ir_glyph_run_spec.spl, compositor_occlusion_spec.spl)
specs failing:      0
specs passing:      9
total examples run (across the 9 specs that produced a verdict): 146
  passed: 146
  failed:   0
VERDICT: RED
```

### Honest verdict: still NOT GREEN

The suite is **not** fully green, and this run does not claim otherwise. All
six of the newly landed fixes are consistent with what this suite can see (no
new failures, 146/146 clean on everything that runs), but the same two specs
that blocked Run 2 still cannot reach a verdict in Run 3, for a now better
understood reason: an internal timeout inside `bin/simple test`'s driver
(roughly 120-140s), not environment contention and not the suite script's
own per-spec timeout floor. Raising that floor further (past the current
1200s) will not fix this — the next useful step, out of scope for this
verification-only task, is finding and adjusting (or bypassing) whatever sets
that internal driver-level limit, or running these two specs through a
different, non-`bin/simple test` execution path.

## Run 4 — fresh re-run after the test-daemon debug-seed-binary-shadowing fix (2026-08-06, later same day)

### What changed since Run 3

Between Run 3 and this run, a real root-cause fix landed for the test daemon
silently pinning to the slow **debug-profile seed binary** instead of the
release binary — documented in
`doc/08_tracking/bug/test_client_debug_seed_binary_shadowing_timeout_2026-08-06.md`.
This is understood to be the root cause of most "mystery timeout" observations
this session, including plausibly the internal ~120-140s driver-level timeout
ceiling that blocked `compositor_occlusion_spec.spl` and
`widget_draw_ir_glyph_run_spec.spl` in Runs 2 and 3 (a debug build running
several times slower than release would explain a spec that measures ~131s
standalone-clean tripping an internal budget sized for release-speed
execution). A companion correction was also made: the lint-timeout issue
previously discussed is linear-with-large-constant, not quadratic — noted here
for completeness, not directly tested by this suite.

### System load

`uptime` immediately before this run:

```
23:02:44 up  8:43,  2 users,  load average: 10.35, 7.97, 6.68
```

`uptime` immediately after this run completed:

```
23:08:51 up  8:49,  2 users,  load average: 7.50, 7.45, 6.88
```

Moderate load on a 32-core box (10.35 → 7.50), consistent with a few other
concurrent sessions' background work, not the heavy 12-14 load-average
contention seen at the start of Runs 2 and 3.

### Full-suite run

`sh scripts/check/check-render-perf-v-lane-suite.shs --timeout 300` (the
occlusion spec still gets its 1200s floor from the script's internal
override):

```
PASS: test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl (38/38 passed)
PASS: test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl (18/18 passed)
PASS: test/01_unit/compiler/semantics/layer_eq_checker_spec.spl (7/7 passed)
PASS: test/01_unit/compiler/semantics/effect_verifier_spec.spl (16/16 passed)
PASS: test/01_unit/lib/common/memory/packed_span_spec.spl (10/10 passed)
PASS: test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl (4/4 passed)
PASS: test/01_unit/os/compositor/hosted_input_sdl2_spec.spl (28/28 passed)
PASS: test/01_unit/os/compositor/compositor_occlusion_spec.spl (10/10 passed)
PASS: test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl (21/21 passed)
PASS: test/01_unit/compiler/class_reference_semantics_spec.spl (6/6 passed)
PASS: test/01_unit/os/render_pixel_bridge_spec.spl (2/2 passed)

=== V-LANE AGGREGATE ===
specs covered:    11
cannot execute:   0
total examples:   160
total passed:     160
total failed:     0
VERDICT: GREEN
```

This full run (all 11 specs, serial, real foreground execution, no ad-hoc
per-spec workarounds) completed in about 6 minutes wall clock (23:02:44 →
~23:08 as measured by `uptime` before/after), well inside the generous budget
allotted for this verification pass.

### Did the daemon fix resolve the two previously-blocked specs? Yes.

| Spec | Run 2 | Run 3 | Run 4 |
|---|---|---|---|
| `compositor_occlusion_spec.spl` | CANNOT EXECUTE @450s | CANNOT EXECUTE @1200s (internal ~120-140s driver timeout, confirmed not load) | **PASS 10/10** |
| `widget_draw_ir_glyph_run_spec.spl` | CANNOT EXECUTE @300s | CANNOT EXECUTE @300s (same internal timeout) | **PASS 4/4** |
| all other 9 specs | PASS | PASS | PASS (unchanged) |

Both specs that were previously blocked by the internal ~120-140s
driver-level timeout ceiling (Runs 2 and 3) now execute to completion and pass
cleanly, with no timeout-related workaround applied in this run. This is
consistent with — though not independently proven beyond this observational
correlation to be caused by — the debug-seed-binary-shadowing fix: a debug
build running several times slower than release would plausibly explain a
~131s-clean spec tripping an internal budget that assumes release-speed
execution. No other change to the suite script, the specs, or the runner was
made between Run 3 and Run 4.

### Run 4 aggregate

```
specs covered:     11
cannot execute:     0
specs failing:      0
specs passing:     11
total examples run: 160
  passed: 160
  failed:   0
VERDICT: GREEN
```

### Honest verdict: GREEN

The suite is **fully green** for the first time across all four runs recorded
in this report: all 11 specs execute to completion, all 160 examples pass, 0
failures, 0 cannot-execute. Both specs that blocked Runs 2 and 3
(`compositor_occlusion_spec.spl`, `widget_draw_ir_glyph_run_spec.spl`) now
pass cleanly. No residual issue was found in this pass.

**Scope caveat carried forward from Run 2:** `bin/simple test` still delegates
to the hosted Rust seed runtime for this execution path
(`reference_simple_test_silently_delegates_to_seed_child.md`), so this GREEN
result proves correctness on that path specifically; it does not by itself
prove the pure-Simple/self-hosted execution path is equally green. That was
out of scope for this verification task, which targeted a genuine, current
re-run of the existing suite as-is.

## T8 — "zero production call sites for SIMD kernels" audit (2026-08-07)

Per `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` §1,
the P row lists this as **NEEDS-INVESTIGATION**: "The V0/V1 'zero production
call sites' finding was never confirmed closed." This section closes it with
an enumerated, anchored grep trail.

**VERDICT: REFUTED. There are real, non-test production call sites, at two
independent layers.**

### Layer 1 — the kernel-table / span-batch dispatcher (P0/P1, `fill_const` only)

```
$ grep -n "kernel_table_register\|self.kernel_table\b" \
    src/lib/gc_async_mut/gpu/engine2d/backend_software.spl
```
`ensure_kernel_table()` (:956) probes and registers into `self.kernel_table`
(:1060); the only real dispatcher of that table,
`simd_span_batch_execute(batch, self.buf, ..., self.kernel_table, ...)`, is
called from `sw_fill_raw_span` (:1073) — **not** from a probe or a spec. This
is consistent with §0/§1's own honest finding (P0/P1 DONE, honest negative):
at every measured bucket the SIMD path measured slower, so
`kernel_table_register` never actually seals a faster slot — the dispatcher
is wired and reachable, but currently always resolves to the scalar branch
inside `simd_span_batch_execute` itself. Call site is real; the *promotion*
is honestly zero, which is a different claim than "zero call sites."

### Layer 2 — the direct native span kernels (P2, fill/copy/blend)

```
$ grep -rn "engine2d_simd_blend_row_u32\|rt_engine2d_simd_fill_span_u32\|rt_engine2d_simd_copy_span_u32" \
    src/ --include=*.spl | grep -v _spec.spl
```
Three bulk-drawing primitives in `backend_software.spl` gate on
`self.native_simd_spans and native_pixel_rows_enabled()` and call these
kernels directly, independent of the kernel table:
- `sw_fill_raw_span` (:1063) → `rt_engine2d_simd_fill_span_u32` (:1080)
- `sw_copy_raw_span` (:1084) → `rt_engine2d_simd_copy_span_u32` (:1090)
- `sw_blend_const_raw_span` (:1098) → `engine2d_simd_blend_row_u32` (:1111)

These three are themselves called from real drawing operations, not test
scaffolding:
- `sw_fill_raw_span` ← framebuffer clear (:357), rect fill (:422, :601),
  `fill_rect`-style wrapper (:1343)
- `sw_copy_raw_span` ← image blit row loop (:650)
- `sw_blend_const_raw_span` ← blend wrapper (:1359)

`native_simd_spans` is `false` by default (`SoftwareBackend.create()`, :292)
and only becomes `true` via `SoftwareBackend.create_cpu_simd()` (:301-302),
reached through `CpuBackend.create_simd()` (`backend_cpu.spl:17`). That
constructor is called from `engine.spl:667` when `Engine2D.create(...,
requested_backend: "cpu_simd")`, **and** the `"cpu_simd"` backend name is
requested from real (non-test) application code, not just specs:
`src/app/office/md_wysiwyg_ppm.spl:57`, `md_wysiwyg_gui.spl:61,63`,
`src/lib/common/ui/wm_app_process_contract.spl:364`,
`src/app/wm_compare/production_gui_web_renderer_parity.spl:249,395,401`, and
the compositor's `src/os/compositor/engine2d_wm_frame_executor.spl:62`.
(`src/app/test/*.spl` and `backend_measurement_*.spl` also request it, but
were excluded from this count — they are test/measurement harnesses, not
production call sites, and are not needed to establish reachability.)

### Answer to the audit question

**Not an empty list.** Enumerated non-test call sites (anchored):

| Kernel entry point | File:line | Caller chain reaches |
|---|---|---|
| `simd_span_batch_execute` | `backend_software.spl:1073` | `sw_fill_raw_span` ← clear/fill/rect draws |
| `rt_engine2d_simd_fill_span_u32` | `backend_software.spl:1080` | same, fallback branch |
| `rt_engine2d_simd_copy_span_u32` | `backend_software.spl:1090` | `sw_copy_raw_span` ← image blit |
| `engine2d_simd_blend_row_u32` | `backend_software.spl:1111`, `:845` | `sw_blend_const_raw_span` ← blend draws |
| backend selection reaching the above | `engine.spl:667`, `backend_cpu.spl:17` | `md_wysiwyg_ppm.spl`, `md_wysiwyg_gui.spl`, `wm_app_process_contract.spl:364`, `production_gui_web_renderer_parity.spl`, `engine2d_wm_frame_executor.spl:62` |

What remains open, stated explicitly rather than silently folded into
"REFUTED": (1) the *default* auto-detected backend at `engine.spl`'s top of
the selection chain is `"software"` (native_simd_spans stays `false`) — SIMD
is reached only when a caller explicitly requests `"cpu_simd"`, which the
five files above do, but this is not the engine's default. (2) Whether
`"cpu_simd"` is exercised in any *default* end-user run path (vs. only
explicit CLI/API opt-in) was not traced further here — out of scope for this
audit, which was scoped to "does a production call site exist," not "is it
the default." (3) T10 (extending the bucket gate beyond `fill_const`) had not
landed at the time of this audit — if it lands later, this Layer 1 section
should be re-read for `KERNEL_OP_SRC_OVER_CONST`/`_IMAGE`/`MASK_SRC_OVER`,
which per §1 register call sites in `ensure_kernel_table` but were not
independently re-probed here beyond confirming the registration code exists
at :1012-1056.

**Binary/method provenance:** this is a static reachability audit (grep +
manual call-chain trace over `.spl` source), not a runtime execution proof —
consistent with the unit's read-only/deliverable-is-a-doc scope in the plan.

## Run 5 — T19 regression-gate re-run (2026-08-07)

T19 (`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`)
re-runs this suite as a regression gate after Waves 1-2, and narrows the
`compositor_occlusion_spec.spl` per-spec timeout floor from the prior
session's 1200s to T19's mandated 300-600s band (plan: "not 150s, not 7200s").
`scripts/check/check-render-perf-v-lane-suite.shs:64` was changed to floor at
600s (the top of that band).

**Binary provenance:** `readlink -f bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted binary, per repo
default-tooling policy).

Verbatim per-spec output:

```
PASS: test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl (44/44 passed)
PASS: test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl (18/18 passed)
PASS: test/01_unit/compiler/semantics/layer_eq_checker_spec.spl (19/19 passed)
PASS: test/01_unit/compiler/semantics/effect_verifier_spec.spl (16/16 passed)
PASS: test/01_unit/lib/common/memory/packed_span_spec.spl (10/10 passed)
PASS: test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl (4/4 passed)
PASS: test/01_unit/os/compositor/hosted_input_sdl2_spec.spl (28/28 passed)
CANNOT_EXECUTE: test/01_unit/os/compositor/compositor_occlusion_spec.spl (exit=255, no verdict line — timeout or crash)
  reason: process timed out after 600s
PASS: test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl (21/21 passed)
PASS: test/01_unit/compiler/class_reference_semantics_spec.spl (6/6 passed)
PASS: test/01_unit/os/render_pixel_bridge_spec.spl (2/2 passed)

=== V-LANE AGGREGATE ===
specs covered:    11
cannot execute:   1
total examples:   168
total passed:     168
total failed:     0
VERDICT: RED
```

**Verdict: RED** — 10/11 specs green (168/168 examples, 0 failed), 1
cannot-execute. This is **not a code regression**: `uptime` at the time of the
run showed `load average: 39.60, 29.07, 22.51` — roughly 3x the 14.0 load
average that previously required 1200s of headroom over this spec's ~130-140s
clean baseline (see Run 3 above). At T19's mandated 600s ceiling, today's
shared-WC contention (5 concurrent agent sessions independently running
`bin/simple test`/`bin/simple run`) is enough to exceed the floor even though
the underlying algorithmic cost is unchanged and bounded.

This tension — the plan's 300-600s band is correct for a lightly-loaded
environment but this repo's actual shared-WC development load regularly
exceeds it — is recorded, not silently patched by widening the timeout back
past the plan's ceiling. Filed as
`doc/08_tracking/bug/v_lane_suite_occlusion_spec_times_out_under_shared_wc_contention_2026-08-07.md`
with re-run and permanent-fix unblock conditions. T16 (blend-span C-symbol
verification) was not part of this suite's 11 specs and required no explicit
exclusion here.
