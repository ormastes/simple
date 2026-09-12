# Web paint path has a wall-clock deadline that makes pixel tests flaky (2026-07-31)

**Status:** OPEN — not fixed, out of scope of the campaign that found it.
Re-verified 2026-08-10: `_web_budget_expired_at`/`_web_budget_expired` (now in
`simple_web_html_layout_renderer_foundation.spl`) and the
`SIMPLE_WEB_RENDER_BUDGET_MS` env override for raising the budget both still
exist, but the override is used only by
`merged_cascade_decl_quota_spec.spl` and
`chrome_stage_comparison_receipts_spec.spl` — not by
`browser_renderer_web_gap_close_spec.spl` (this doc's repro) or by the test
harness generally, so the wall-clock deadline is still armed, unraised, and
untest-gated for ordinary pixel specs. The underlying flake mechanism is
unchanged.
**Severity:** any pixel-verifying spec on the web renderer is non-deterministic
under concurrent load. This produces FALSE FAILURES that look like real
rendering regressions.

## Symptom

`_web_budget_expired()` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`
enforces a WALL-CLOCK paint deadline. Under system load it trips even for
trivial pages (a 2-node document), aborting paint early. Affected pixels come
back as background white where a blend/fill was expected.

## Reproduction observed

`browser_renderer_web_gap_close_spec.spl`, unchanged between runs:

| Run | Conditions | Result |
|---|---|---|
| 1 | 3 other agent lanes compiling concurrently | `6 total, 2 passed, 4 failed` |
| 2 | quieter machine, immediate retry, NO code change | `6 total, 6 passed, 0 failed` |

The 4 failures were: single-element opacity compositing, `isolation: isolate`
parse, filter grayscale, filter brightness — i.e. whichever examples happened to
paint when the deadline tripped, not a consistent set. A real logic bug would
fail the same examples every time.

## Why this matters beyond the flake

A wall-clock budget inside a paint path means correctness depends on machine
load. This is the third distinct "looks like a failure but isn't" mechanism found
in one day, and they must not be conflated:

1. `ERROR: test daemon timed out` (~1885 log lines) — transient, retry once.
2. `Process timed out` (exactly 1938 lines) — the deterministic compiler hang,
   `doc/08_tracking/bug/compiler_cross_tier_diamond_import_hang_2026-07-31.md`.
3. **This one** — the spec RUNS and REPORTS a normal `Results:` line with real
   assertion failures. It is the most dangerous of the three because it looks
   exactly like a genuine regression, and a `Results:` line is normally the
   authoritative signal.

## Guidance until fixed

- Re-run any web pixel spec once before believing a failure, and say in reports
  whether a failure survived a retry.
- Do NOT baseline a web pixel spec against origin while other lanes are
  compiling — the comparison is not valid under differing load.
- A wall-clock deadline is the wrong mechanism for a deterministic paint path.
  Preferred fix: a work/step budget, or make the deadline opt-in for interactive
  use and disabled under test.

Found by: unified 2D campaign, web-gap lane; confirmed independently by the
coordinator (fail 2/6 then pass 6/6 with no code change).

## Note 2026-09-12 — one more spec now arms the override

- Status: OPEN (2026-09-12) — mechanism unchanged, coverage of the override widened by one spec
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`

The 2026-08-10 re-verification above lists the specs that actually raise
`SIMPLE_WEB_RENDER_BUDGET_MS` as `merged_cascade_decl_quota_spec.spl` and
`chrome_stage_comparison_receipts_spec.spl`. Add a third:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl`,
which compares the public engine2d lane against the software oracle byte-for-byte
and therefore cannot tolerate either side's deadline tripping. It now arms the env
override at 600000 and passes the same 600000 explicitly as the oracle's
`budget_ms` argument, because the two lanes take their budget through different
channels and raising only one still leaves the comparison load-dependent.

This does not fix the underlying defect: the wall-clock deadline is still armed
and unraised for ordinary pixel specs, and it is still per-spec opt-in rather than
a harness default. Recorded so the eventual fix knows which specs already
compensate by hand.
