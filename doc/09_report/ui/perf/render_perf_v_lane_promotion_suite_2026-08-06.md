# Render-Perf V-Lane Correctness/Promotion Suite — Aggregate Report (2026-08-06)

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
- **`compositor_occlusion_spec.spl` — CANNOT EXECUTE, newly observed here.**
  Times out at 150s with literal `Process timed out` in the runner log and no
  `SPEC FILE VERDICT` line at all — this is a genuine hang/very-slow-path, not
  a false-timeout artifact (ruled out the shared-batch-timeout trap by
  re-running it alone). This is a new, previously-unflagged defect this
  report surfaces: the spec cannot currently prove anything, positive or
  negative, and needs investigation (not performed here — out of this task's
  scope) before it can be counted toward promotion.
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
