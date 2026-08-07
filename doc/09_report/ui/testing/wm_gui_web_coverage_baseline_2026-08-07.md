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

## U4.4 / U4.5 closure — 2026-08-07

Targets per plan: U4.4 = `simple_web_html_layout_renderer_layout.spl` (2613
lines) + `simple_web_html_layout_renderer_core.spl` (3098 lines) +
`containment.spl` (167 lines), line target >=90%. U4.5 =
`simple_web_html_layout_renderer_paint_layout.spl` (3121 lines) +
`simple_web_html_layout_renderer_paint_primitives.spl` (1349 lines), line
target >=85%. Binary: `readlink -f bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed).

### containment.spl (U4.4) — MET, artifact-backed

Baseline run (`containment_contain_spec.spl` alone, `SIMPLE_COVERAGE_OUTPUT`
artifact `containment.spl` rows counted directly): **87% (28/32 lines)**.
Uncovered lines identified from the artifact (rows present for 28 of the 32
denominator lines; the missing 4 never appear as rows at all):
`containment.spl:43-45` (the mid-string token-match branch of
`contain_has_token`, only reachable with a multi-token `contain` value where
the target token is not the last segment) and `containment.spl:126` (the
`state.cached.contains_key(node_id)` branch inside
`layout_contain_mark_dirty`).

New spec `test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_coverage_closure_spec.spl`
(2 `it` blocks, real oracle assertions on `node_contains_layout/paint/style`
and `layout_contain_compute`/`layout_contain_mark_dirty` return/state values,
no assertion-free calls) closes lines 43-45. Re-measured (same command,
fresh artifact): **96% (31/32 lines)** — exceeds the >=90% target.

Line 126 stays uncovered despite two spec cases that call
`layout_contain_mark_dirty` on a node with an existing cache entry (the
`contains_key == true` branch is *demonstrably* taken — `state.cached[nid]`
flips to `false` and the next `layout_contain_compute` call recomputes,
proving the branch ran) — the collector never emits a row for that exact
line. This reads as an instrumentation-granularity artifact of the coverage
collector on a single-line `if COND:` immediately followed by a mutating
statement, not a gap in test coverage. Not filed as a new bug; folds into
the existing collector-gap tracking in
`doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`.

Sabotage: `contain_has_token`'s mid-string match arm
(`containment.spl:43`) was disabled (`and false` appended) in the live
worktree, target spec re-run -> `Results: 2 total, 1 passed, 1 failed`,
failure message `expected subject to be truthy, got false` on exactly the
multi-token-match example. Restored from a pre-sabotage copy, byte-identical
(`sha256sum` matched, `git diff origin/main:...containment.spl` empty);
re-run -> `Results: 2 total, 2 passed, 0 failed`.

### `_layout.spl` + `_core.spl` (rest of U4.4) and `_paint_layout.spl` +
### `_paint_primitives.spl` (U4.5) — NOT MET, honest gate report

These four files total 10,181 lines. The only spec in the tree carrying
`# @cover` headers for all of them,
`simple_web_html_layout_renderer_coverage_spec.spl`, hits the test runner's
hard **120s per-file timeout** every time it was run this session (both via
`bin/simple test ... --coverage` and via
`test_runner_single.spl ... --no-session-daemon --sequential --coverage`) —
it never reaches its `coverage:` lines, so no line-percentage for these four
files was obtainable through it. Smaller existing specs in the same
directory that reference the layout/paint modules
(`simple_web_html_layout_renderer_scan_index_space_spec.spl`,
`simple_web_html_layout_renderer_module_split_spec.spl`) either report
coverage for a *different* file (`simple_web_html_layout_renderer_foundation.spl`,
1421 lines, 3%) or fail before completing, so they do not substitute.

Per the plan's own honesty rule ("if a unit is genuinely unachievable
without branch coverage, land an honest gate report ... rather than
padding"), this session reports: **no artifact-backed line-coverage number
for `_layout.spl`, `_core.spl`, `_paint_layout.spl`, or
`_paint_primitives.spl` was obtained; the >=90%/>=85% line targets are
correspondingly UNMET (not attempted-and-failed, but unmeasured) for these
four files.** No `Dict.len()`/assertion-free padding was used to manufacture
a number. This is a gap for a follow-up unit that first fixes or
works around the 120s per-file test-runner timeout for large `@cover` sets
(e.g. splitting `simple_web_html_layout_renderer_coverage_spec.spl`'s GPU/
tile-lane `it` blocks, which are the likely long pole, into a separate file
from the layout/paint-primitive ones) before attempting closure specs.

### Disk

`df -h /`: 238G free before, 238G free after (no cargo/bootstrap run).

## U4.4 / U4.5 — timeout unblocked, real measurements obtained — 2026-08-07 (session 2)

Follow-up to the "NOT MET, honest gate report" section above. The blocker was
the coverage spec (`simple_web_html_layout_renderer_coverage_spec.spl`) dying
at the test runner's 120s hard timeout before printing any `coverage:` line
for the four target files.

### `slow_it` fix verified to genuinely raise the ceiling

Commit `423c0c46b834f4caec6a7fd7a479806515b7b6f0` (earlier this session) fixed
`run_one_via_daemon`'s deadline computation in
`src/app/test_runner_new/test_runner_client.spl` to consult
`effective_timeout_secs()` (600s floor when the spec source contains
`"slow_it "`) per-path inside the daemon-lane request loop, not once per batch
from the un-bumped CLI default. Verified empirically, not assumed:

- Baseline (no `slow_it` in the file): `bin/simple test <spec> --coverage
  --no-cache`, `SIMPLE_COVERAGE=1` -> **`Process timed out` / `error:
  test-runner: file timed out`, `Duration: 120210ms`, exit 1, zero `coverage:`
  lines, zero example output.** Confirms the 120s death is still real.
- After marking one `it` block `slow_it` (`use std.spec.{describe, it,
  slow_it, expect}` + the "blends a soft box shadow" example) and re-running
  the identical command: **completed in `real 3m44.877s`, exit 0, `Results: 28
  total, 28 passed, 0 failed`, 10 `coverage: <path> NN% (H/T)` lines printed,
  and a 898,856-byte `SIMPLE_COVERAGE_OUTPUT` artifact (8,254 rows) backing
  them.** The fix lifts the ceiling for the daemon lane as designed.

### Real per-file line coverage (artifact-backed, `/tmp/u44_cov_slowit.sdn`
### then `/tmp/u44_cov_closure1.sdn` after the closure example below)

| Target file | Line coverage | Target | Met? |
|---|---|---|---|
| `simple_web_html_layout_renderer_layout.spl` (U4.4) | 40% (658/1634) | >=90% | **NOT MET** |
| `simple_web_html_layout_renderer_core.spl` (U4.4) | 54% (1123/2075) | >=90% | **NOT MET** |
| `simple_web_html_layout_renderer_paint_layout.spl` (U4.5) | 42% (610/1432) | >=85% | **NOT MET** |
| `simple_web_html_layout_renderer_paint_primitives.spl` (U4.5) | 35% (319/907) | >=85% | **NOT MET** |

(Line counts in this table are the coverage collector's instrumentable-line
denominators, which are smaller than raw `wc -l` — e.g. `_layout.spl` is 2613
raw lines but 1634 measured lines — consistent with how `containment.spl`'s
denominator, 32, was already smaller than its raw line count in the prior
section.)

These are the first artifact-backed line-coverage numbers ever obtained for
these four files — previously "unmeasured", now measured and honestly UNMET.
Closing a ~2000-line and a ~1400-line module family each from ~40-54% to 90%
and ~85% respectively is multiple further closure units of work (the same
scale as U4.1-U4.6 combined); this session did not attempt to pad past that
with assertion-free calls or inflate the denominator.

### One real closure example landed (paint_primitives.spl), sabotage-verified

Added `"enters fb_outline_clip via a box with a CSS outline set"` to
`simple_web_html_layout_renderer_coverage_spec.spl` (new fixture
`_outline_doc()`: a box with `outline: 2px solid #ff0000` and no border).
`fb_outline_clip` (`simple_web_html_layout_renderer_paint_primitives.spl:905-914`)
was 0/10 lines covered; `fb_border`/`fb_border_sides` (dead code, zero
callers anywhere in `browser_engine/`) were confirmed unreachable and are not
targeted. Oracle: 3 distinct ARGB values (page-bg white, box-bg blue, outline
red) over a 32x24 frame -- first measured via a throwaway `bin/simple run`
JIT probe (`/tmp/probe_outline.spl`), then independently confirmed under the
interpreter engine actually used by `bin/simple test`.

Re-measured after adding the example: `paint_primitives.spl` 34% (311/907) ->
**35% (319/907)**, `Results: 29 total, 29 passed, 0 failed`.

Sabotage (in-tree, per the shared-WC worktree caveat -- `git worktree add
HEAD` gives an incomplete checkout here since `src/lib/gc_async_mut/**` is
staged-but-uncommitted): `fb_outline_clip` was made an unconditional
`return fb` no-op. Re-run: `Results: 29 total, 28 passed, 1 failed`, failure
`expected 2 to equal 3` on exactly `"enters fb_outline_clip via a box with a
CSS outline set"` -- every other example, including the other 4 paint-
primitive examples, stayed green. Restored; `sha256sum` of the file matched
both the pre-sabotage value and `git show origin/main:<path>` exactly
(`698622002e7bcce616ccf5f283e0b230b00f6ccafe76de2838fb980de6d2dbb9`), and
`git diff --no-index` against the origin/main blob was empty.

### Remaining gap

`_layout.spl`, `_core.spl`, `_paint_layout.spl` now have zero new closure
examples this session (only `paint_primitives.spl` got one, as a proof of the
now-unblocked methodology). Reaching >=90%/>=85% on all four files is a
multi-unit follow-up; not scoped or attempted here beyond unblocking
measurement itself and landing one verified example. Tracked in
`doc/08_tracking/bug/simple_web_html_layout_renderer_layout_paint_coverage_gap_2026-08-07.md`.

### Provenance / disk

Binary: `readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed, per repo policy for `test`). `df -h /`: 238G free before, 238G
free after (no cargo/bootstrap run). Spec runs took ~3m45s-3m47s each (well
under the new 600s slow_it ceiling and the 900s tool budget).
