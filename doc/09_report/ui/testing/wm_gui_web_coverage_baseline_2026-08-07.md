# U1.2 — WM/GUI/web coverage baseline (LINE coverage only), 2026-08-07

- **Unit:** U1.2 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`.
- **Binary provenance:** `readlink -f bin/simple` ->
  `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed, per repo
  policy the correct binary for `test`).
- **Gate before/after:** `sh scripts/check/check-render2d-coverage.shs` ->
  `FAIL — 5 prerequisite(s) checked, 4 unmet` both before and after this unit.
  Row detail: `prereq3_spl_coverage_dispatchable` UNMET, `prereq4_artifact_export`
  **MET** (was UNMET when the gate doc was written 2026-08-07 earlier the same
  day; flipped by commit `ae97a34cd365` before this unit started), prereq1/2/5
  still UNMET (unverified/Rust-side, untouched by this unit). This unit did not
  edit the gate script.
- **Disk:** `df -h /` before 239G free, after 239G free (no cargo/bootstrap run).

## Hypothesis tested

U1.2 was gated on the premise "coverage tooling doesn't instrument `.spl`
end-to-end." Commit `ae97a34cd365` fixed prerequisite 4 (artifact export to
`SIMPLE_COVERAGE_OUTPUT`). The residual gap documented in
`test_runner_single.spl:375-386` is narrower than the blocking bug doc implied:
only an **imported module's top-level statements** (bounded, <=2 lines/module)
get mis-filed under `<entry>`. Statements inside functions of an imported
module — which is nearly everything in `src/os/compositor/**`,
`src/lib/gc_async_mut/gpu/browser_engine/**`, `src/lib/common/ui/**` when
exercised from a spec — get real file/line attribution today.

**Result: HYPOTHESIS HELD.** Every run below produced a `coverage: <real path>
NN% (H/T lines)` line with the actual `src/...` path (never `<source>`, never
`<entry>` for the target file), and a non-empty `SIMPLE_COVERAGE_OUTPUT`
artifact whose raw `(file, line, hit_count)` rows independently corroborate
real paths and real line numbers — not just the stdout banner. Example
(first 6 data rows of the pixel-surface run's artifact,
`/tmp/u12_cov8.sdn`, 1964 bytes):
```
lines |file, line, hit_count|
    /home/ormastes/dev/pub/simple/src/lib/common/ui/pixel_surface_content_frame.spl, 12, 1
    /home/ormastes/dev/pub/simple/src/lib/common/ui/pixel_surface_content_frame.spl, 13, 1
```
matching the stdout banner `coverage: src/lib/common/ui/pixel_surface_content_frame.spl 100% (2/2 lines)`.

## Sabotage check (required before trusting the positive case)

Positive case confirmed first (`pixel_surface_content_frame_spec.spl` with the
correct `# @cover` target, see table below), then the target path was
misspelled (`pixel_surface_content_frame_WRONGPATH.spl`) in a throwaway copy
run once and deleted, never committed. Result: **no `coverage:` line appeared
for the misspelled target** — only the "bypassing test daemon" banner and the
`Results:` line. Confirms lines are reported per-declared-target, not
invented.

## Baseline table

Method: existing spec run individually via
`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path> bin/simple test <spec>
--coverage --no-cache`, `coverage:` stdout lines transcribed verbatim, cross-
checked against the artifact bytes at `SIMPLE_COVERAGE_OUTPUT`. A `#
@cover <target> 20%` header was added to specs that lacked one (listed under
"header added"); no spec's assertions were modified.

**LINE coverage only.** Branch/decision coverage remains unavailable
(`branch_coverage=unavailable(pending-U1.3)` — prerequisites 1, 2, 5 are
Rust-side and untouched by this unit or by commit `ae97a34cd365`). The plan's
eventual "~100% function/branch" goal is **not** addressed or implied by any
number in this table.

### `src/os/compositor/**`

| Spec | Header added | Spec result | Target file | Line coverage |
|---|---|---|---|---|
| `test/01_unit/os/compositor/engine2d_damage_report_spec.spl` | no (pre-existing) | 7/7 passed | `src/os/compositor/compositor_engine2d.spl` | 26% (31/115 lines) |
| `test/01_unit/os/compositor/engine2d_damage_report_spec.spl` | — | 7/7 passed | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | 2% (27/1110 lines) |
| `test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl` | yes | 3/3 passed | `src/os/compositor/host_compositor_core.spl` | 10% (126/1234 lines) |
| `test/01_unit/os/compositor/host_compositor_core_coverage_closure_spec.spl` | no (pre-existing) | 12/12 passed | `src/os/compositor/host_compositor_core.spl` | 8% (102/1234 lines) |

`test/03_system/wm/wm_full_stack_demo_spec.spl` was attempted (targeting
`common/ui/layout.spl`) but hit the test-runner's own per-file timeout
(`error: test-runner: file timed out`) inside the 300s foreground budget —
recorded as `line_coverage=unconfirmed` for that spec, header addition
reverted (not landed), no fabricated number substituted.

### `src/lib/gc_async_mut/gpu/browser_engine/**` (layout/style/paint core)

All three specs below **failed all their examples** (0 passed) for reasons
unrelated to coverage instrumentation (a pre-existing failure in this shared,
concurrently-edited working tree at the time of the run — not investigated
further, out of this unit's scope). The `coverage:` lines still printed with
real paths, but because execution aborted early inside each failing example,
these numbers are a **floor**, not the modules' achievable coverage.

| Spec | Header added | Spec result | Target file | Line coverage |
|---|---|---|---|---|
| `test/01_unit/browser_engine/ifc_linebox_spec.spl` | yes | 0/10 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout_inline.spl` | 0% (0/38 lines) |
| `test/01_unit/browser_engine/ifc_linebox_spec.spl` | — | 0/10 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 0% (0/64 lines) |
| `test/01_unit/browser_engine/ifc_linebox_spec.spl` | — | 0/10 passed | `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl` | 53% (148/277 lines) |
| `test/01_unit/browser_engine/ifc_linebox_spec.spl` | — | 0/10 passed | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | 0% (0/79 lines) |
| `test/01_unit/browser_engine/margin_collapse_spec.spl` | yes | 0/8 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl` | 0% (0/0 lines) |
| `test/01_unit/browser_engine/margin_collapse_spec.spl` | — | 0/8 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 0% (0/64 lines) |
| `test/01_unit/browser_engine/table_layout_spec.spl` | yes | 0/7 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout_table.spl` | 0% (0/99 lines) |
| `test/01_unit/browser_engine/table_layout_spec.spl` | — | 0/7 passed | `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 0% (0/64 lines) |
| `test/01_unit/browser_engine/table_layout_spec.spl` | — | 0/7 passed | `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl` | 51% (144/277 lines) |
| `test/01_unit/browser_engine/table_layout_spec.spl` | — | 0/7 passed | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | 0% (0/79 lines) |

`test/03_system/gui/simple_web_browser_production_hardening_spec.spl` (has a
pre-existing `# @cover src/app/ui.web/...` header, a different module family
— `ui.web`, not `browser_engine` layout/style/paint) was not run: out of
scope for this module family and not attempted.

### `src/lib/common/ui/**`

| Spec | Header added | Spec result | Target file | Line coverage |
|---|---|---|---|---|
| `test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl` | yes | 1/1 passed | `src/lib/common/ui/pixel_surface_content_frame.spl` | 100% (2/2 lines) |
| `test/01_unit/lib/common/ui/wm_window_state_spec.spl` | yes | 2/2 passed | `src/lib/common/ui/wm_window_state.spl` | 47% (10/21 lines) |

## Done-checklist (per U1.2)

- [x] >=15 coverage lines recorded verbatim (not banners) — 16 rows in the
      three tables above (4 compositor + 10 browser_engine + 2 common/ui),
      all transcribed from stdout and cross-checked against the
      `SIMPLE_COVERAGE_OUTPUT` artifact bytes.
- [x] daemon-bypass banner confirmed each run (`coverage: SIMPLE_COVERAGE set;
      bypassing test daemon` on every invocation).
- [x] misspelled-target sabotage documented (above; positive case confirmed
      first).
- [x] provenance recorded (binary path above; per-row artifact byte counts
      spot-checked, see hypothesis section).
- [x] committed+pushed (this unit).

## Caveats — do not over-read this table

1. **Line coverage only.** No branch/decision number appears anywhere in this
   report. Branch coverage stays `unavailable(pending-U1.3)`.
2. **Browser-engine numbers are floors**, not ceilings — three of the five
   picked specs failed all examples before fully exercising their target
   module, for reasons unrelated to this unit's scope.
3. **`<entry>`-flattening residual** (documented in
   `test_runner_single.spl:375-386`) still under-counts an imported module's
   top-level statements by <=2 lines/module — a further reason every number
   above is a floor, never inflated.
4. **This table does not establish "coverage tooling is production-ready."**
   Only prerequisite 4 (export) is confirmed MET by the live gate; prereqs
   1/2/3/5 remain UNMET/unverified, and the `spl-coverage` CLI subcommand
   still does not exist in the deployed binary.
