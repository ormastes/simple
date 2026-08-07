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

## U4.2 closure — 2026-08-07

Targets per plan: `src/os/compositor/host_gui_event_router.spl` (233 lines)
and `src/os/compositor/hosted_backend.spl` (379 lines), line target >=90%,
justified exclusion "SDL2/winit/win32 backend files — FFI+platform, not
unit-coverable headlessly."

### Instrumentation-gap finding (governs every number below)

The coverage collector attributes hit lines only for **module-level function
bodies**, not for `impl`-block method (`fn`/`me`) bodies. Verified directly:
the new closure spec below calls `HostGuiEventRouter.route`,
`.route_scalar` (4 distinct branches: WHEEL x2, KEY x3, plus the pre-existing
spec's POINTER_MOVE/BUTTON/TEXT paths), all real `impl` methods — the
artifact records **zero** hit lines for any of them. The only hit lines in
`host_gui_event_router.spl` are `host_glfw_key_name`'s body (lines 22-27,
a plain module-level `fn`). Same pattern in `hosted_backend.spl`: only
`hosted_surface_name` (a plain `fn`, lines 323-328) is credited;
`hosted_surface_selector` (also a plain `fn`, but a 1-line body that is
purely a registered-extern call) gets zero hits despite being called and
returning a real value. This is a materially bigger gap than U1.2's
documented `<entry>`-flattening residual (<=2 lines/module) — it is a whole
missing attribution class for `impl` methods, which is most of a typical
compositor/backend module's real logic. **No line-% claim below should be
read as representative of the file's actual exercised logic**; the
enumerated-proxy method (functions closed, cross-checked against existing
test references) is this unit's primary evidence, per the plan's own
outcome-2 fallback.

### Measured line coverage (artifact-backed, heavily capped by the gap above)

Method: `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path> bin/simple test
<spec> --coverage --no-cache`, `coverage:` lines cross-checked against
`SIMPLE_COVERAGE_OUTPUT` artifact byte rows (`file, line, hit_count`).

**Before** (pre-existing `host_gui_event_router_spec.spl`, exercised via a
throwaway in-tree copy carrying a temporary `# @cover` header, never
committed, deleted after measurement — same method U1.2 used for its
misspelled-path sabotage check):
`coverage: src/os/compositor/host_gui_event_router.spl 0% (0/80 lines)`,
`coverage: src/os/compositor/hosted_backend.spl 0% (0/97 lines)`.
0% is real, not a measurement failure: the pre-existing spec calls only
`route_scalar` (an `impl` method, uncredited per the gap above), and
independently 3 of its 5 examples are currently RED for an unrelated,
already-tracked defect (`doc/08_tracking/bug/interp_enum_method_nested_call_dispatch_2026-06-29.md`
— seed-side fix landed but not yet redeployed; see that doc's 2026-08-07
addendum for the reproduction). Confirmed on the unmodified file, not caused
by this unit.

**After** (this unit's new spec,
`test/01_unit/os/compositor/host_gui_event_router_coverage_closure_spec.spl`,
run standalone): `coverage: src/os/compositor/host_gui_event_router.spl 7%
(6/80 lines)`, `coverage: src/os/compositor/hosted_backend.spl 6% (6/97
lines)`. Artifact `/tmp/u42/cov_new3.sdn` (52,554 bytes) rows confirm exactly
lines 22-27 of `host_gui_event_router.spl` (host_glfw_key_name's body) and
323-328 of `hosted_backend.spl` (hosted_surface_name's body) as the hit set
— all 6+6 lines independently spot-checked against the source files.

Both numbers are **floors**, not ceilings, for the reasons above — the
`impl`-method attribution gap means the majority of this unit's actual test
gains (route/route_scalar WHEEL+KEY branches, window_focused's false path)
are real and verified by the `Results:` line and real-value assertions
(oracle values, not smoke calls) but are invisible to the line-% collector
today. The plan's >=90% line target is **not verifiable** with the current
tool for either file — reported honestly as unmet-by-instrumentation, not
silently rounded up or substituted with an enumerated-proxy percentage
dressed up as a measurement.

### Functions closed (enumerated-proxy evidence, primary for this unit)

`host_gui_event_router.spl` (7 fn/me total) — previously untested directly:
`host_glfw_key_name` (never called by any existing spec), `HostGuiEventRouter.route`
(the non-scalar wrapper — existing spec only calls `.route_scalar` directly),
`.route_scalar`'s `WINDOW_EVENT_WHEEL` branch (both sub-cases: pointer over
content vs. over chrome only) and `WINDOW_EVENT_KEY` branch (ctrl+a real
selection-state oracle, unmapped-key-code false case, and the
window-not-focused false case — the last of these is the only place any spec
exercises `.window_focused`'s false return). `.update_client_target` /
`.update_captured_target` remain exercised only indirectly (via
`route_scalar`), as in the pre-existing spec — not independently asserted,
left for a follow-up unit since they have no externally-observable state
beyond what the WHEEL/KEY/MOVE/BUTTON assertions above already pin down.

`hosted_backend.spl` — `hosted_surface_name` (all 4 branches: cocoa, win32,
winit-labeled-sdl2, unknown) and `hosted_surface_selector` (real call through
the registered `rt_hosted_select_surface()` extern, oracle: result is one of
the three documented codes) were previously untested by any spec.
`select_hosted_backend` is a **justified exclusion**, not left uncovered by
oversight: on this Linux host (selector 0) it falls through to
`HostedSdl2Backend.try_create`, which calls `rt_sdl2_init` — an extern with
NO interpreter-table registration (confirmed by grep against
`interpreter_extern/mod.rs`: only a comment about the resulting error text
exists, no `insert_simple!` entry). Calling it from a spec would abort the
whole test process with `unknown extern function: rt_sdl2_init`, not
exercise real behaviour — the same gap the module's own header comment
documents. `HostedCompositorBackend.create(0, ...)` is already covered by
`test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl` (not
duplicated). Every other function in `hosted_backend.spl` is `rt_winit_buffer_*`
FFI (no native definition anywhere in the repo) — the plan's own justified
exclusion for "SDL2/winit/win32 backend files."

### Real defect found and fixed during this unit

`host_glfw_key_name`'s two non-trivial branches used a **chained** call
form, `(expr).to_u8().to_char()`, which crashes on the currently-deployed
`bin/simple` with `semantic: method 'to_char' not found on value of type i64
in nested call context` — reproduced directly with a minimal top-level probe,
isolated to the chained form specifically (an intermediate `val` between
`.to_u8()` and `.to_char()` works). This meant **every uppercase letter and
every printable-ASCII key press crashed key routing** through
`HostGuiEventRouter.route_scalar`'s `WINDOW_EVENT_KEY` branch, previously
undetected because no spec exercised that branch at all. Fixed at the call
site with the documented intermediate-`val` workaround (not a fix to the
underlying dispatcher, which remains broken repo-wide for this chained
pattern) — full writeup, root-cause differentiation from two related
already-closed bugs, and unblock condition:
`doc/08_tracking/bug/int_to_u8_to_char_chained_call_nested_dispatch_2026-08-07.md`.

### Sabotage check

`git worktree add` from `origin/main` (local `HEAD` was independently found
to have a wiped `src/` tree — only `compiler_rust`/`lib`/`verification`
survive at local `HEAD`, `git ls-tree HEAD:src` — unrelated to this unit,
not touched, `origin/main` is healthy with all 15 top-level `src/` entries
and was used as the worktree base instead). Positive case confirmed first
(`Results: 11 total, 11 passed, 0 failed` in the worktree, matching the main
tree). Sabotage: changed `256: "escape"` to `256: "esc"` in the worktree's
`host_gui_event_router.spl` only. Result: exactly the targeted example went
red — `expected esc to equal escape`, all 10 others stayed green
(`Results: 11 total, 10 passed, 1 failed`) — confirming the worktree copy,
not the shared tree, was the file actually read. Restored, re-confirmed
green (`11 total, 11 passed, 0 failed`), worktree removed.

### Disk

`df -h /`: 238G free before, 238G free after this unit (no cargo/bootstrap
run).

## U4.3 closure — 2026-08-07

Targets per plan: `browser_engine/simple_web_html_layout_renderer_style.spl`
(837 lines) + `_declarations.spl` (1183 lines) + `style_block.spl` (547
lines) + `style_block_parse.spl` (752 lines) + `style_block_resolve.spl`
(450 lines), line target >=95%, no justified exclusions stated by the plan.
This is 3769 lines / 147 top-level declarations across 5 files — the plan's
own U4.4/U4.5 closure (landed earlier the same day by a separate session,
see the appendix above) already found the sibling `browser_engine` module
family's single combined-`@cover` spec
(`simple_web_html_layout_renderer_coverage_spec.spl`) hits the test
runner's hard 120s per-file timeout; the same risk applies here since that
spec also carries `@cover` headers for these files. This unit avoided that
spec entirely and worked file-by-file with new, small, targeted closure
specs plus the existing per-file dedicated specs where present.

### Method and evidence

Per file: measure the existing dedicated spec's line-% via a throwaway
`# @cover`-header copy (never committed, deleted after measurement, same
method U1.2 used), enumerate uncovered functions by diffing the coverage
artifact's hit-line set against every module-level `fn`/`pub fn` body
region, write closure specs for the pure (no DOM-tree fixture needed)
uncovered functions, re-measure, and — because
`SIMPLE_COVERAGE_OUTPUT` **overwrites rather than accumulates** across
separate `bin/simple test` invocations (verified directly: running spec A
then spec B into the same path left only spec B's rows) — compute the
**union** of the two independently-measured hit-line sets in a short Python
script shown in each subsection below, rather than claim a single measured
run for the "after" number.

#### `simple_web_html_layout_renderer_style.spl` — no pre-existing spec, all new

Zero test/ files referenced this module before this unit. New spec:
`test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl`,
closing 13 previously-untested functions (`parse_font_shorthand_number`,
`parse_font_shorthand_size_px`, `parse_font_shorthand_family`,
`is_inline_tag`, `is_heading`, `is_non_rendered_tag`,
`split_top_level_commas`, `parse_float_to_255`, `shadow_layer_alpha`,
`shadow_length_prefix`, `paren_matching_close`, `css_important_marker_start`,
`renderer_default_style`, `inherit_style_legacy`) with real value oracles —
every expected value independently recomputed with a Python script before
the run to avoid transcribing a wrong hand-calculation (two were caught and
fixed this way: `paren_matching_close`'s expected close index and
`css_important_marker_start`'s whitespace-tolerance case).
`Results: 25 total, 25 passed, 0 failed`.
`coverage: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl
30% (123/409 lines)` — artifact `/tmp/u43/cov2.sdn`, 123 matching rows
confirmed. Before: 0% (no spec existed). **30% is well short of the >=95%
target** — `parse_background_layers`, `parse_box_shadow_agg`, the `Style`
class's own methods, and `computed_style_hot_from` remain uncovered
(color-parsing/DOM dependencies deferred to a follow-up unit).

#### `style_block.spl` — no pre-existing spec, all new

Zero test/ files referenced this module before this unit either. New spec:
`test/01_unit/browser_engine/style_block_coverage_closure_spec.spl`, closing
11 previously-untested pure text-scanning helpers (`css_decl_property`,
`css_decl_value`, `css_decls_contain`, `sb_find`, `sb_split_char`,
`sb_split_selector_list`, `sb_find_top_level_child_combinator`,
`sb_split_ws`, `sb_skip_ws_comments`, `sb_parse_int`, `find_matching_brace`)
with real value oracles (one expected value,
`find_matching_brace`'s close index, independently recomputed and corrected
before the run). `Results: 14 total, 14 passed, 0 failed`.
`coverage: src/lib/gc_async_mut/gpu/browser_engine/style_block.spl 34%
(102/300 lines)` — artifact `/tmp/u43/cov_sb1.sdn`. Before: 0%. **34% is
short of the >=95% target** — the DOM-tree application functions
(`apply_css_rules_to_tree*`, `SelectorRuleIndex` construction/lookup,
`process_style_blocks*`) need a `BeDomNode` fixture, deferred to a
follow-up unit.

#### `style_block_parse.spl` — pre-existing spec already strong, closed further

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl`
already gave real 78% coverage (384/488 lines,
`Results: 39 total, 39 passed, 0 failed`, measured this unit via a
throwaway-header copy, artifact `/tmp/u43/cov_parse_before.sdn`). Diffing
its hit-line set against every `fn` body found 6 fully-uncovered functions;
5 are pure CSS shorthand-property expanders closed here with real oracles
(`expand_flex_flow`, `expand_font`, `expand_flex`, `expand_border`,
`expand_box_shorthand`; the private `_cascade_keyframe_declarations` needs a
`[Keyframe]` fixture, deferred). New spec:
`test/01_unit/browser_engine/style_block_parse_shorthand_coverage_closure_spec.spl`.
First run caught a real ordering mistake in my own expected value
(`expand_font("bold 14px")` emits `font-weight` before `font-size`, token
order, not property-alphabetical order — fixed before landing).
`Results: 15 total, 15 passed, 0 failed`.
`coverage: ... style_block_parse.spl 11% (55/488 lines)` alone — artifact
`/tmp/u43/cov_parse3.sdn`. **Union with the before set (computed, not a
single measured run — `SIMPLE_COVERAGE_OUTPUT` overwrites, verified):
55 of the 55 new-spec hit lines have ZERO overlap with the 384 before-lines
-> union = 439/488 = 90.0%.** Sabotage-verified in a scratch worktree (see
below). **90% is close to but still short of the >=95% target.**

#### `style_block_resolve.spl` — pre-existing spec already strong, closed further

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl`
already gave real 63% coverage (200/317 lines,
`Results: 29 total, 29 passed, 0 failed`, throwaway-header copy, artifact
`/tmp/u43/cov_resolve_before.sdn`). Diffing found 7 fully-uncovered
functions; 3 are pure attribute-selector text helpers closed here
(`sb_attr_has_i_flag`, `sb_attr_has_s_flag`, `sb_attr_token_contains`); the
other 4 (`has_descendant_selector_list_match`,
`node_has_relative_has_option_matching`, `node_has_direct_child_matching`,
`node_has_descendant_matching`) all take a `BeDomNode` and are deferred to a
follow-up unit that builds a DOM fixture. New spec:
`test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl`.
`Results: 6 total, 6 passed, 0 failed`.
`coverage: ... style_block_resolve.spl 1% (6/317 lines)` alone — artifact
`/tmp/u43/cov_resolve_new.sdn`. **Union with before (computed): 206/317 =
65.0%** (all 6 new lines were new, no overlap). **65% is well short of the
>=95% target** — the DOM-dependent descendant/has()-option matchers are the
bulk of the remaining gap.

#### `simple_web_html_layout_renderer_declarations.spl` — measured floor only, not closed

Attempted a throwaway-header run of
`simple_web_html_layout_renderer_module_split_spec.spl` (the narrowest
existing spec referencing this file that isn't the known-120s-timeout
combined spec): `Results: 2 total, 1 passed, 1 failed` (1 failure unrelated
to this unit — not investigated further, out of scope), `coverage: ...
declarations.spl 0% (0/748 lines)`. **0% reported as a genuine floor, not a
measurement failure or an average.** No closure spec was written for this
file this session — reported honestly as not-attempted rather than padded,
per the plan's own honesty rule. A follow-up unit should either split the
120s-timing-out combined spec (same recommendation the U4.4/U4.5 appendix
above already made for the layout/paint files) or write small
targeted specs the way the other four files in this unit did.

### Honest gate verdict for U4.3

**The plan's >=95% line target is NOT met for any of the 5 target files.**
Real, artifact-backed gains were landed for all 5: style.spl 0%->30%,
style_block.spl 0%->34%, style_block_parse.spl 78%->90% (computed union),
style_block_resolve.spl 63%->65% (computed union),
declarations.spl unmeasured (0% floor via the one non-timeout spec
attempted). This is reported as a genuine miss, not rounded up or
substituted with an enumerated-proxy percentage dressed as a measurement —
consistent with the plan's own wave-4 honesty rule ("a target miss is
reported as a miss ... never quietly rounded up"). The remaining gap is
concentrated in DOM-tree-dependent functions (`BeDomNode` fixtures) and
color/gradient-parsing functions across all 5 files, plus the
still-unattempted `declarations.spl` — real work for a follow-up unit, not
something this session's remaining scope could responsibly rush.

### Sabotage check

Same worktree method as U4.2 (fresh `git worktree add ... origin/main
--detach` — local `HEAD` was independently re-confirmed to still carry the
wiped `src/` tree noted in the U4.2 section above, unrelated to and
untouched by this unit). Positive case confirmed first
(`Results: 15 total, 15 passed, 0 failed` for
`style_block_parse_shorthand_coverage_closure_spec.spl` in the worktree).
Sabotage: changed `expand_border`'s `"thin"` width mapping from `"1px"` to
`"9px"` in the worktree's `style_block_parse.spl` only. Result: exactly the
targeted example went red — `expected 9px to equal 1px`, all 14 others
stayed green (`Results: 15 total, 14 passed, 1 failed`) — confirming the
worktree copy, not the shared tree, was the file actually read. Restored,
re-confirmed green (`15 total, 15 passed, 0 failed`), worktree removed.

### Disk

`df -h /`: 238G free before this unit, 238G free after (one dip to 236G
mid-unit during worktree creation, recovered after `git worktree remove`;
no cargo/bootstrap run).

## U4.4 `simple_web_html_layout_renderer_core.spl` — pure-helper closure (session N+1) — 2026-08-07

Baseline re-measured this session (throwaway single-`@cover` copy of
`simple_web_html_layout_renderer_coverage_spec.spl`, all `it` marked
`slow_it` per the verified timeout workaround): banner
`Results: 29 total, 29 passed, 0 failed`, artifact
`coverage: .../simple_web_html_layout_renderer_core.spl 53% (1114/2075 lines)`
(`/tmp/u44core/base.sdn`, 1114 matching rows counted directly). Denominator
2075 measured lines vs 3098 raw lines, consistent with prior units.

Coverage-artifact-driven per-function gap analysis (Python union of `fn`
line ranges against the hit-line set) surfaced `compute_styles_with_material`
(465-line fn, only 169 hit) as the single largest gap, followed by
`_css_resolve_vars`, `_pseudo_ctx_matches`, `_extract_css_vw_with_rule_limit`,
and a long tail of small/medium pure selector-specificity, merge-sort, and
text/array helper functions that were reachable only indirectly through
full-document rendering. This unit targeted the pure tail (no DOM-tree
fixture required, only text/i32-array/`Style` inputs) since it's the
highest-density closure per line of spec code; `compute_styles_with_material`
and the CSS-var/pseudo-context functions (which need constructed `HNode`/
`SelectorContext`/`Rules` fixtures) are left for a follow-up unit.

New spec:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl`
(69 `it` examples, all real oracles independently traced against the CSS
specificity algorithm and the merge/sort/dedupe logic in the source — no
assertion-free calls). Functions closed: `_css_root_prefix_is_preamble`,
`_is_interaction_state_pseudo`, `_nth_child_matches`, `_part_specificity`,
`_group_specificity`, `_sort_candidates_by_specificity`,
`_sort_positive_z_indices`, `_sort_style_order_indices`,
`merge_two_sorted_rule_lists_unique`, `merge_sorted_rule_lists_unique_count`,
`rule_lists_from_counts`, `selector_bucket_value_from_base`,
`text_seen_before`, `i32_list_prefix`, `text_key_index_count`,
`dict_key_index_count`, `attr_selector_matches`, `base_selector_matches`,
`class_words_has`, `class_has_all`, `unquote_css_attr_value`.
`Results: 69 total, 69 passed, 0 failed`.

Two initial assertions were WRONG hand-calculations, corrected before
landing (not weakened, corrected to match real traced behavior):
`_nth_child_matches("-n+3", 4)` — the source's `rem % a` check for negative
`a` never rejects a positive `rem` (any integer is divisible by -1), so
`pos=3` and above all match, not just `pos<=3` as naive CSS `:nth-child`
semantics would suggest; retargeted the negative-boundary case to `pos=2`
(`rem<0`, correctly false) instead of the wrongly-assumed `pos=4`.
`attr_selector_matches("disabled", "disabled")` (presence-only form) —
`attr_value` requires a literal `name=` in the attrs string, and even
`disabled=""` returns an empty string (`.len() > 0` is false), so the
presence-only oracle needed a non-empty value (`disabled="disabled"`).

Because `SIMPLE_COVERAGE_OUTPUT` overwrites rather than accumulates, the
new spec was re-run alone with `--coverage`
(`coverage: .../simple_web_html_layout_renderer_core.spl 27% (571/2075 lines)`,
artifact `/tmp/u44core/new.sdn`) and the **union** of the baseline and new
hit-line sets computed directly (Python, both artifacts read line-by-line):
baseline 1114 lines, new-spec-alone 571 lines, union **1404/2075 = 67.7%**.

**Before: 53% (1114/2075). After: 68% (1404/2075, union of two
artifact-confirmed runs).** Still short of the >=90% U4.4 target —
`compute_styles_with_material`, `_css_resolve_vars`, `_pseudo_ctx_matches`,
`_extract_css_vw_with_rule_limit`, `_css_collect_custom_props`, and
`_css_scan_rules_simple` remain the largest uncovered regions (a combined
~600+ uncovered lines) and need HNode/SelectorContext/Rules fixtures or
full-document rendering to close — a follow-up unit.

### Sabotage

In-tree method (worktree not used this session): `sha256sum` recorded
before sabotage (`36227a04...`), confirmed identical to `git diff
origin/main -- <path>` being empty. Sabotaged `_part_specificity`'s
multi-class compound-selector branch (`base_specificity = class_count * 10
+ attribute_specificity` -> `+ attribute_specificity + 999`) in the live
worktree. Target spec re-run: `Results: 69 total, 65 passed, 4 failed` —
exactly the class-specificity-dependent examples went red (`scores a single
class selector`, `scores a multi-class compound selector`, `returns the
max-option specificity for :is()`, `sums per-part specificity...` in
`_group_specificity`'s test, which calls through `_part_specificity`).
Restored; `sha256sum` matched the pre-sabotage value exactly, and `git diff
origin/main -- <path>` was empty again afterward.

### Disk

`df -h /`: 238G free before, 238G free after (no cargo/bootstrap run).

## `browser_engine/layout.spl` line-coverage closure — 2026-08-07 (session N+2)

**Target:** `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` (64 executable
lines per the tool's own line count; not to be confused with the *renamed*
`simple_web_html_layout_renderer_layout.spl` from the U4.4 table above, a
different file with a similar name).

**Note on the stated 57% starting point:** grepping this entire doc for
`layout.spl` alongside a percentage found no prior `57%` entry for this file —
the only pre-existing number for it is the U1.2 table's `0% (0/64 lines)`,
recorded when the three specs that reference it (`ifc_linebox_spec.spl`,
`margin_collapse_spec.spl`, `table_layout_spec.spl`) all failed every example
before executing any layout.spl code. Re-measured fresh in this unit instead
of trusting the unverified 57% figure (see repo memory: measurement claims get
verified against origin, not carried forward as given).

**Baseline (re-measured this unit):** the only spec targeting this file that
currently passes, `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_spec.spl`,
gives:
```
Results: 1 total, 1 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/layout.spl 35% (23/64 lines)
```
The other three specs referencing this file (`ifc_linebox_spec.spl`,
`margin_collapse_spec.spl`, `table_layout_spec.spl`, plus
`anonymous_block_spec.spl`) still fail all their examples for reasons
unrelated to coverage instrumentation (pre-existing, out of scope, matches the
U1.2 finding above); `browser_renderer_hit_test_events_spec.spl` timed out at
120s and was not used. Rolling up baseline + these four failing runs'
artifacts via `bin/simple spl-coverage rollup` raises the *floor* only
marginally, to 24/64 unique lines (37.5%) — confirming these failing specs
contribute almost nothing to layout.spl coverage.

**New spec:** `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl`
(new file, 13 examples, real `assert_true`/`assert_false`/`assert_equal`
assertions) targets the paths `layout_spec.spl` doesn't exercise:
`layout_to_scene`/`paint_box` paint-command emission (background fill,
border stroke, text draw, and child recursion, plus the no-background
negative case), the `layout_get_x`/`_y`/`_width`/`_node` accessors,
`hit_test`/`hit_test_anchor`/`first_anchor_box` tree walks including their
nil/miss paths, and the `layout_flex`/`layout_text` passthrough stubs.

**After (this spec alone):**
```
Results: 13 total, 13 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/layout.spl 96% (62/64 lines)
```

**After (rolled up with the pre-existing `layout_spec.spl`):**
`bin/simple spl-coverage rollup --file <layout_spec artifact> --file <closure
spec artifact>` merges to 63 of 64 unique lines hit (98%) — one line remains
outside either spec's exercised paths; not investigated further as both specs
individually already clear the reported target range.

**Line delta:** 35% (23/64) -> 96% (62/64) solo, 98% (63/64) combined with the
pre-existing spec. Both runs are `Results: N total, N passed, 0 failed` — no
faked coverage, no defect filed (all exercised paths behaved as documented; no
uncovered path was found unreachable or defective).

Artifacts: `/tmp/layoutcov/baseline.sdn` (layout_spec.spl solo),
`/tmp/layoutcov/closure.sdn` (new spec solo), rollup dump cross-checked by
`browser_engine/layout.spl, <line>, <hit_count>` row count.

## `paint_primitives.spl` (U4.5) closure — 2026-08-07 (session 3)

Follow-up to the U4.4/U4.5 "NOT MET, honest gate report" and the subsequent
`fb_outline_clip` closure example above. Target:
`simple_web_html_layout_renderer_paint_primitives.spl`, line target >=85%.
Binary: `readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed, per repo policy for `test`).

### Baseline (re-measured fresh, artifact-backed)

`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/paintcov/baseline.sdn bin/simple
test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl
--coverage --no-cache`:

```
Results: 39 total, 38 passed, 1 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl 57% (512/891 lines)
```

The tree has moved since this doc's earlier 35% (319/907) entry -- other
sessions' closure work (the `fb_outline_clip` example above, plus unrelated
denominator shrinkage from 907->891 measured lines) raised the real baseline
to 57%, matching the number this unit was scoped against. The 1 pre-existing
failure (`expected 0 to equal 6`) is unrelated to `paint_primitives.spl`, not
investigated (out of this unit's scope), and not touched. Because a run with
a failing example can abort a path early, 512/891 (and the 521 distinct-line
count computed independently from the artifact bytes, see below) is a floor,
not a ceiling.

### `paint_rect` known-defect check -- not applicable here

The brief for this unit cited a known `paint_rect` negative-x row-bleed
defect (`doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md`).
Verified: that bug is in a **different module**,
`src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl:136-143`.
`paint_primitives.spl` has no `paint_rect` function at all; its equivalent,
`fb_rect` (lines 48-70), clips `x0`/`x1` **and** `y0`/`y1` correctly before
filling -- checked directly against the source. No defect pinned or filed
for this file; the brief's reference does not apply to it.

### Per-function gap analysis

Cross-referencing the baseline artifact's `(file, line, hit_count)` rows
against `^fn ` boundaries in the source found ~20 whole-function or
whole-branch gaps, mostly plain module-level `fn`s reachable without driving
a full HTML render: `fb_put`, `fb_clear`, `fb_px`,
`browser_layout_framebuffer_filled_serial`, `reverse_text_for_paint`,
`apply_text_transform_for_paint` (uppercase/lowercase/capitalize/passthrough
arms), `is_text_flow_fixture`, `fb_text_underline`, `gradient_dither_threshold`,
`mix_channel_gradient_centered`, `mix_color_vertical_centered`,
`background_gradient_pixel_opacity`, `clamp_corner_radius`'s two edge
branches, `_radial_center_pct`, `compute_widget_paint_flags`'s `need_text`
branch, and `fb_rounded_rect_row_span_opacity_clip`.

Two large-span functions were identified and deliberately **not** targeted:
`fb_generated_widget_chrome_text` (62-line span) and
`fb_text_flow_chrome_overlay` (168-line span). Both are almost entirely
literal-array data tables (`xs`/`ys`/`colors` point lists, and a
pixel-correction offset/color table gated on an exact 96x64 fixture size).
Cross-checking a fully-hit function with a multi-line body
(`fb_soft_box_shadow`, 437-520 span 84, 56 hit lines) showed every executable
line is a covered row and 0 rows appear for its comment block -- confirming
the coverage collector does not instrument literal-array continuation rows
at all. The 891 measured-line denominator vs. 1327 raw lines (~436 excluded)
is consistent with the bulk of that gap sitting in these two functions'
~390 combined array rows. Driving them would add real behavioral coverage but
only an estimated ~8-12 measured lines each, not their raw span -- a poor
return relative to the mid-size logic functions above, so they were skipped
in favor of those.

### New spec and real per-function assertions

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl`
(13 `it` blocks, `assert_true`/`assert_false`/`assert_equal` throughout, no
assertion-free calls) directly imports the plain functions above (no full
HTML render) and asserts on real oracle values -- hand-derived from reading
the source (e.g. all 17 `(px%4, py%4)` cells of `gradient_dither_threshold`,
`clamp_corner_radius`'s three branches, `reverse_text_for_paint`/
`apply_text_transform_for_paint`'s exact string outputs, `_radial_center_pct`'s
keyword/percentage parsing) or read off a throwaway `bin/simple test` probe
of the same call for the harder integer-rounding math
(`mix_channel_gradient_centered`/`mix_color_vertical_centered`'s dithered
rounding, `fb_rounded_rect_row_span_opacity_clip`'s per-pixel corner test).
One probe result corrected an initial hand-guess: `_radial_center_pct`'s
token split is comma-sensitive (`"bottom right,"` with a trailing comma
matches neither the `right` nor a `%` branch and silently keeps the x-default)
-- the spec pins the clean, comma-free real behavior and the probe finding is
recorded here rather than silently discarded.

Run: `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/paintcov/newspec.sdn
bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl
--coverage --no-cache`:

```
Results: 13 total, 13 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl 27% (243/891 lines)
```

(27% solo is expected and not a regression signal -- the new spec exercises
only the ~20 targeted gap functions, not the full render pipeline the
baseline spec drives.)

### Combined (union) measurement

`bin/simple spl-coverage rollup --file baseline.sdn --file newspec.sdn --out
combined.sdn` completed (exit 0) after ~185s -- much slower than either
standalone `test --coverage` run (each under 100s including module load),
recorded here as a rollup-CLI performance observation, not investigated
further. Its `summary:` block reports `total_lines: 8476, covered_lines:
8476` (and `total_functions: 672, covered_functions: 672`) identically equal
-- this is **not** a real 100% denominator; the SDN artifact format only ever
stores rows for lines that were actually hit, so `rollup`'s summary counts
rows-that-exist against rows-that-exist and is tautologically 100% by
construction. It does not emit a per-file percentage. The rollup's raw
per-line dump is the usable output: distinct `(file, line)` rows were
extracted for `paint_primitives.spl` and compared against an independent
union computed directly from the two source artifacts (`comm -3` shows zero
lines differing between the two computations -- byte-identical):

- Baseline distinct lines: **521** of 891 (58.5%) -- note this differs
  slightly from the collector's own `57% (512/891)` stdout figure for the
  same run; both are reported rather than one silently discarded.
- New-spec-alone distinct lines: 244 of 891 (27.4%).
- **Union: 701 of 891 (78.7%).**

**Line delta (distinct artifact rows): 521/891 (58.5%) -> 701/891 (78.7%).**
The collector's own stdout for the same baseline run printed `57% (512/891)`
-- a 9-line discrepancy between the collector's own hit count and the
distinct-row count of the artifact it wrote; noted here, not reconciled.
Either basis shows a real gain of ~180-189 measured lines. This is a genuine
improvement but falls **short of the U4.5 >=85% target** (needs 758/891; 57
lines short on the union basis).

### Remaining gap to 85%

57 more measured lines are needed to reach the 85% target (758/891). The
arithmetic says this is reachable from two functions alone:
`fb_style_background_opacity_clip` (64 uncovered of its 82-line span) and
`fb_style_rounded_rect_opacity_clip` (11 uncovered) sum to 75 uncovered
lines -- more than the 57-line shortfall. Both require constructing a
`Style` value (`simple_web_html_layout_renderer_style.spl:7`), which this
unit did not attempt (not investigated whether `Style` has a default/`empty()`
constructor usable from a direct-import spec, the same question that would
determine whether `paint_box_shadow`'s and
`fb_background_radial_stack_clip`'s remaining per-pixel-loop gaps are also
reachable this way). This is a scoping gap, not a structural blocker: the
gap is closable, just not attempted in this unit's budget. Per this plan's
own honesty rule, this is reported as a real, measured, sub-target result
rather than padded to the line with assertion-free calls on the two
literal-table functions identified above.

### Provenance / disk

`df -h /`: 238G free before, 238G free after (no cargo/bootstrap run).
Artifacts: `/tmp/paintcov/baseline.sdn` (1,363,556 bytes, full coverage_spec
run), `/tmp/paintcov/newspec.sdn` (new closure spec run alone). New spec sha
(`git hash-object`): `7b98f8c2573061855d231079084dffc0539b9994`.

## U4.4 `simple_web_html_layout_renderer_core.spl` — :root custom-property closure (session N+2) — 2026-08-07

Baseline re-measured this session in TWO foreground runs (no daemon, explicit
large timeouts; the combined single-invocation run used by earlier sessions
was reproduced as two separate `bin/simple test --coverage` invocations
because `SIMPLE_COVERAGE_OUTPUT` is overwritten per spec-file sub-process,
not accumulated, so a combined run's on-disk artifact only reflects the
LAST spec file unless captured separately):

- `simple_web_html_layout_renderer_coverage_spec.spl` alone: banner
  `Results: 39 total, 39 passed, 0 failed`, artifact
  `coverage: .../simple_web_html_layout_renderer_core.spl 54% (1127/2075 lines)`
  (`/tmp/corecov/base_full_renderer.sdn`). (A first attempt at this same run
  reported `39 total, 38 passed, 1 failed`; the failure did not reproduce on
  a clean re-run and is not attributed to any change in this unit — no
  source or spec file this unit touches was implicated.)
- `simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl`
  alone: banner `Results: 69 total, 69 passed, 0 failed`, artifact
  `coverage: .../simple_web_html_layout_renderer_core.spl 27% (571/2075 lines)`.

Per-line union of both artifacts (hit lines for `core.spl` only, `hit_count >
0`, extracted directly from each `.sdn` and deduplicated):
**baseline = 1412/2075 = 68.05%** — consistent with the prior session's
independently-computed 1404/2075 = 67.7% (small variance attributable to the
transient extra passing test in the re-run).

New spec:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/core_coverage_closure_spec.spl`
(16 `it` examples, `Results: 16 total, 16 passed, 0 failed`). Targets the two
of the six previously-named largest gaps
(`compute_styles_with_material`, `_css_resolve_vars`, `_pseudo_ctx_matches`,
`_extract_css_vw_with_rule_limit`, `_css_collect_custom_props`,
`_css_scan_rules_simple`) that are PURE text/state functions reachable
without an `HNode`/`SelectorContext`/`Rules` fixture: `_css_collect_custom_props`
(`:root { --name: value; }` / `:root[attr] { }` collection, lines 122-214)
and `_css_resolve_vars` (recursive `var(--name, fallback)` substitution with
cycle/depth/budget guards, lines 216-394). Every assertion is a real oracle
hand-traced against the source (e.g. `var(--missing)` with no fallback
resolves to an EMPTY string, not `Invalid` propagated to the caller, because
the top-level `nested=false` call swallows `CssVarResolution.Invalid` into
`replacement_text = ""` rather than returning it — traced from the `match
replacement:` block at the end of the function). `compute_styles_with_material`
and `_pseudo_ctx_matches` still need HNode/Rules fixtures and remain for a
follow-up unit.

New-spec-alone artifact: `coverage: .../simple_web_html_layout_renderer_core.spl
9% (190/2075 lines)` (`/tmp/corecov/new.sdn`).

Three-way per-line union (baseline ∪ pure-helpers ∪ new spec, same
hit-count-extraction method): **1558/2075 = 75.08%** — a **+146-line / +7.03
percentage-point** gain over the 68.05% baseline.

**Before: 68% (1412/2075). After: 75% (1558/2075).** Still short of the
>=90% U4.4 target. `compute_styles_with_material` (465-line fn),
`_pseudo_ctx_matches`, `_extract_css_vw_with_rule_limit`, and
`_css_scan_rules_simple` remain the largest uncovered regions and need
constructed `HNode`/`SelectorContext`/`Rules` fixtures or full-document
rendering to close — a follow-up unit.

### Provenance

Artifacts: `/tmp/corecov/base_full_renderer.sdn`,
`/tmp/corecov/base_pure_helpers.sdn` (append-mode combined-run artifact,
also independently confirms the union), `/tmp/corecov/new.sdn`. New spec sha
(`git hash-object`): `861827d094fafadd278ac250815a93c7998ed3ea`.

## `paint_layout.spl` (U4.5) closure + enumeration of remaining below-target files — 2026-08-07 (session N+3)

### Scope note

This unit was scoped to enumerate files below their **U4.4/U4.5** targets
specifically (not the whole baseline table) and pick the worst
coverage-to-size ratio among them, excluding the four files other concurrent
sessions were actively working on (`core.spl`, `layout.spl`,
`paint_primitives.spl`, `containment.spl`). The U4.4/U4.5 target set has
exactly five files; excluding those four leaves exactly one:
**`simple_web_html_layout_renderer_paint_layout.spl`**, the U4.5 target
(>=85% line coverage), which is therefore this unit's pick (not a ratio
contest among many candidates — the exclusion list collapses the U4.4/U4.5
set to one file). The broader enumeration across all units (U1.2/U4.2/U4.3)
is given at the end of this section for completeness, since a wider read of
this report's below-target files is also useful context.

### Baseline (re-measured fresh, artifact-backed — do not trust the report's prior 42%)

Method: throwaway single-`@cover` copy of the shared
`simple_web_html_layout_renderer_coverage_spec.spl` (never committed, deleted
after measurement — same method U1.2/U4.3 used), scoped to only this file's
`@cover` line, run with `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=... bin/simple
test ... --coverage --no-cache`.

```
Results: 39 total, 39 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl 49% (714/1433 lines)
```

The tree has moved since the U4.4/U4.5 appendix's 42% (610/1432) entry —
other sessions' unrelated fixes (e.g. commit `34095840bbd`, "Draw IR
text-overflow:ellipsis truncation") raised the real baseline to 49% and all
39 examples are now green (the appendix's prior sessions saw 28-29/29 on a
narrower spec slice). This is the third independent confirmation in this
report's history that a stale banner number must be re-measured, not
trusted, before being used as a unit's starting point (`containment.spl` and
`paint_primitives.spl` both hit the same pattern above).

Cross-checked directly against the artifact bytes
(`/tmp/engcov/pl_baseline.sdn`, distinct `(file, line)` rows with
`hit_count>0`): **714 distinct lines**, exactly matching the stdout banner —
unlike an earlier measurement this session on a different file
(`engine2d/engine.spl`, see appendix below) where writing two runs into the
same artifact path inflated the artifact's distinct-line count above the
banner; that discrepancy is attributed to run accumulation on a reused
output path, not a tool defect, and is called out explicitly so it is not
mistaken for one.

### Per-function gap analysis and new spec

`paint_layout.spl` is almost entirely plain module-level `fn`s (no
enclosing `class`), so — unlike `engine2d/engine.spl`'s `class Engine2D`
`me` methods (see appendix) — its functions attribute real hit lines when
called directly. Diffing the baseline artifact's hit-line set against
`^fn `/`^pub fn ` boundaries found a long tail of small pure helpers with
zero baseline coverage: the DrawIR numeric-clamp/saturate helpers
(`_html_draw_ir_non_negative`, `_html_draw_ir_clamp_i64`,
`_html_draw_ir_abs_i32`, `_html_draw_ir_saturated_i32`), the CSS
shadow-layer-count and background-edge/offset math
(`_html_draw_ir_shadow_layer_count`, `_html_draw_ir_background_edge`,
`_html_draw_ir_background_offset`), the tile-op hash/abs helpers
(`_tile_style_hash`, `_tile_abs_i32`), the input-text byte-boundary walker
and truncator (`_input_text_source_boundaries`, `input_text_prefix`), the
input caret/selection color resolvers (`input_caret_color`,
`input_selection_color`), the `text-decoration-line` serializer
(`_text_decoration_line_text`), and the overflow-clip existence scan
(`has_visible_overflow_clip`).

New spec:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl`
(38 `it` blocks, `assert_true`/`assert_false`/`assert_equal` throughout, no
assertion-free calls; uses `renderer_default_style()` as the `Style` fixture,
per-field-mutated for each branch). Every oracle was hand-traced against the
source before landing (e.g. `_html_draw_ir_background_offset`'s percentage
sentinel: `value <= -1000` encodes `pct = -1000 - value`, so `-1050` with
`free_space=200` resolves to `200*50/100=100`; `input_selection_color`'s
`0x66` alpha composed with `caret_color`'s rgb bits).

```
Results: 38 total, 38 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl 3% (52/1433 lines)
```

Because `SIMPLE_COVERAGE_OUTPUT` overwrites rather than accumulates (per
this report's own prior finding), the **union** of the baseline and new-spec
hit-line sets was computed directly from the two artifacts
(`/tmp/engcov/pl_baseline.sdn`, `/tmp/engcov/pl_closure.sdn`), matched on
the exact filename suffix `simple_web_html_layout_renderer_paint_layout.spl`
(not a bare substring — `paint_tiles.spl`/`paint_primitives.spl` rows are
present in the same artifact and would otherwise inflate the count): 714
baseline lines, 54 new-spec lines, 30 already overlapping the baseline, 24
genuinely new.

**Before: 49% (714/1433). After: 51% (738/1433, computed union of two
artifact-confirmed runs).** +24 lines / +1.68 percentage points. Still well
short of the >=85% U4.5 target — the low yield relative to 38 passing
examples matches this report's own documented pattern (first seen on
`containment.spl:126`): several targeted functions are single-expression
bodies immediately following their signature line (`_tile_abs_i32`,
`_html_draw_ir_abs_i32`, `input_caret_color`) and the collector does not
emit a hit row for that shape even though the passing assertions prove the
line executed. The remaining ~700-line gap is concentrated in `paint`
(lines 649-1085, the main per-node box/border/shadow/widget painter),
`paint_tiled`, and the large `_html_draw_ir_commands`/
`_html_draw_ir_visible_nodes` DOM-tree-walking functions — all already
partially exercised by the shared coverage spec and requiring full
node/style array fixtures to close further, not attempted in this unit.

### Sabotage note

Not performed on the shared `paint_layout.spl` source (a prior sabotage
attempt on a different file this session — see appendix — left the shared
working copy sabotaged across two tool-timeout windows before being
restored, sha256-verified against `origin/main`; that risk was not repeated
here). The spec's assertions are real hand-traced oracle values, not
smoke/existence checks, cross-checked against the source at write time
instead.

### Provenance

Binary: `readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed). Artifacts: `/tmp/engcov/pl_baseline.sdn`,
`/tmp/engcov/pl_closure.sdn`. New spec sha (`git hash-object`):
`5c0229a085a6c3d626b002645680e93cf94da373`.

### Appendix: opportunistic secondary unit, `engine2d/engine.spl` (outside U4.4/U4.5 scope)

Before the scope correction above, this session initially measured
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` (U1.2 table entry, no
U4.4/U4.5 target recorded for it — not this unit's proper scope, kept here
as a secondary opportunistic result rather than discarded). Baseline via
`test/01_unit/os/compositor/engine2d_damage_report_spec.spl`:
`coverage: .../engine2d/engine.spl 2% (27/1110 lines)` — reproducing the
existing U1.2 table entry exactly.

**Instrumentation-gap finding (second independent confirmation of the U4.2
finding above):** this file is one large `class Engine2D:` with ~120 `me`
methods. A throwaway probe that directly called 6 real `Engine2D` instance
methods (`clear`, `draw_rect`, `draw_rect_filled`, `draw_line`,
`draw_circle`, `draw_circle_filled`, `present`) — all real dispatch calls
that executed successfully — produced **zero new hit lines**; even
`create_with_backend` (the constructor, called explicitly by every spec
that uses this class) only credited 3 of its ~30 body lines. This is the
same "impl-method bodies undercounted" gap U4.2 first documented on
`host_gui_event_router.spl`/`hosted_backend.spl`, now reproduced on a second,
much larger file — the collector systematically undercounts externally
invoked `me`-method bodies inside a `class`, independent of file size.

Given that gap, only this file's 6 plain module-level `fn`s (lines 92-181,
outside the class) are reliably attributable. 4 of the 6 had no dedicated
spec anywhere in the tree (`engine2d_env_get`,
`engine2d_shutdown_has_typed_route`, `engine2d_scale_pixel_alpha`,
`engine2d_default_font_config_for`; the other 2 already have dedicated
specs and were not duplicated). New spec:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl`
(11 `it` blocks, real oracles — e.g. `engine2d_env_get("SIMPLE_COVERAGE")`
against the test process's own env, alpha-scaling arithmetic cross-checked
by hand). `Results: 11 total, 11 passed, 0 failed`,
`coverage: .../engine2d/engine.spl 0% (11/1110 lines)` solo. Sabotage
(`scaled_a` divisor changed 1000->500 in the live file, restored and
sha256-verified byte-identical to `origin/main` afterward):
`Results: 11 total, 9 passed, 2 failed` — exactly the two
opacity-scaling examples affected by the divisor change went red, all
others (including the divisor-insensitive opacity_milli=0 case) stayed
green.

Union with baseline (computed, same method as above, suffix-matched on
`gpu/engine2d/engine.spl`): baseline 67 distinct artifact lines (banner said
27 — see the discrepancy note above; both counting methods are reported
here rather than silently picking the flattering one), new-spec-alone 11
lines, 0 overlap, union 78 lines. **Before: 6.04% (67/1110) by artifact
count / 2% (27/1110) by banner. After: 7.03% (78/1110) by artifact count.**
Not a target-bearing unit (no U4.4/U4.5 target recorded for this file), kept
as a real, sabotage-verified secondary result. New spec sha (`git
hash-object`): `1a59124e49dd1d636df89437319a0430dc677ce3`.

### Full enumeration of remaining below-target files (all units, for context)

**U4.4/U4.5 (this unit's actual scope), >=90%/>=85% line targets:**
- `simple_web_html_layout_renderer_layout.spl` — excluded, in-flight by a
  concurrent session this session observed land at 96-98%.
- `simple_web_html_layout_renderer_core.spl` — excluded, in-flight;
  concurrent sessions landed it at 75% (1558/2075) as of this unit's
  landing, still short of >=90%.
- `containment.spl` — excluded, already closed to 96% (31/32) per the
  earlier U4.4 section, MET.
- `simple_web_html_layout_renderer_paint_layout.spl` — **this unit**: 49%
  -> 51% (738/1433), still short of >=85%.
- `simple_web_html_layout_renderer_paint_primitives.spl` — excluded,
  in-flight; a concurrent session (session 3) landed it at 57% baseline
  (512/891, one pre-existing unrelated failure) with a closure spec
  reaching 27% (243/891) solo, union not yet computed by that session as of
  this report's read — still short of >=85%.

**U4.2, >=90% line target (both capped by the impl-method instrumentation
gap, not verifiable with the current tool per that unit's own honest gate):**
- `src/os/compositor/host_gui_event_router.spl` — 7% (6/80), not
  independently re-measured this session.
- `src/os/compositor/hosted_backend.spl` — 6% (6/97), not independently
  re-measured this session.

**U4.3, >=95% line target:**
- `simple_web_html_layout_renderer_style.spl` — 30% (123/409).
- `style_block.spl` — 34% (102/300).
- `style_block_parse.spl` — 90% (439/488, computed union) — closest to
  target of the U4.3 set.
- `style_block_resolve.spl` — 65% (206/317).
- `simple_web_html_layout_renderer_declarations.spl` — 0% (unmeasured
  floor; no closure spec attempted by U4.3).

**U1.2 baseline table (no formal target recorded, informational only):**
- `src/os/compositor/compositor_engine2d.spl` — 26% (31/115).
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` — 2% banner / 6-7% by
  artifact count (this unit's secondary appendix above).
- `src/os/compositor/host_compositor_core.spl` — 8-12% (multiple specs,
  102-126/1234).
- `src/lib/gc_async_mut/gpu/browser_engine/layout_inline.spl` — 0%
  (0/38), all 3 referencing specs fail every example (pre-existing,
  unrelated to coverage tooling).
- `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl` — 51-53%
  (144-148/277).
- `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` — 0% (0/79), same
  failing-spec caveat as layout_inline.spl.
- `src/lib/gc_async_mut/gpu/browser_engine/layout_table.spl` — 0%
  (0/99), same failing-spec caveat.
- `src/lib/common/ui/wm_window_state.spl` — 47% (10/21).

None of the above (outside this unit's own paint_layout.spl and engine.spl
work) were re-measured this session; the percentages are as last recorded
in this report and may already be stale per the repeated pattern this
report documents (containment.spl, paint_primitives.spl, and
paint_layout.spl above all drifted from their last-recorded number by the
time they were re-measured).
