# Render-Perf V-Lane Correctness/Promotion Suite — Aggregate Report (2026-08-06)

> **Status note (added after Run 2, same day):** Run 1 below is preserved
> verbatim as the historical record. Run 2 (bottom of this doc) re-ran the
> suite after both Run-1 blockers were independently fixed. Run 2 also
> **retracts** the Run-1 claim that `compositor_occlusion_spec.spl`'s timeout
> was "ruled out" as a false-timeout/shared-batch artifact — that claim was
> wrong; the timeout was real per-process contention, not a hang. See the Run
> 2 section for the correction and for a newly observed residual issue
> (`widget_draw_ir_glyph_run_spec.spl`).

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
