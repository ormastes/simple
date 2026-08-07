# WM / GUI / Web HTML-CSS System-Test & Coverage Plan (2026-08-07)

**Directive (verbatim):** "make sspec system tests for wm, gui, and analysis web
html/css elements needed to gui fully test functionallity ... add tests and make
coverage almost 100% on funciton/branch. from wm/gui to vulkan. fully tests with
container since it is headless test environment."

**Audience:** an executing agent on a weaker model (Sonnet/Haiku). Every design
decision is made HERE. Do not redesign; execute units as written. When a spec
rightly fails against a real defect, leave it RED and file the bug (see
`.claude/rules/testing.md`) — never soften an assertion.

## 0. Scope boundary with the sibling plan

A sibling plan, `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
covers everything BELOW the compositor-backend interface: engine2d raster,
paint/SIMD kernels, Vulkan/GPU backends. **This plan stops at the compositor
interface**: WM behaviour, GUI/web layout+style, and the two browser-engine
exits — DrawIR (`common.ui.draw_ir.DrawIrComposition`, produced by
`simple_web_layout_render_html_draw_ir`) and rasterized readback
(`Engine2DReadback` / `[u32]` pixels from
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`).
Pixel oracles in this plan treat engine2d/CPU raster as a trusted black box;
do NOT plan or write units for engine2d internals here. If a pixel oracle
fails and triage points below the compositor interface, file the bug and
cross-reference the sibling plan instead of fixing it in this campaign.

## 1. Verified ground truth (investigated 2026-08-07, all file:line checked)

### 1.1 Existing WM/GUI system-test surface
- Spec clusters: `test/03_system/gui/` (83 specs, 18 WM-related),
  `test/03_system/os/wm/` (6), `test/03_system/wm/` (1:
  `wm_full_stack_demo_spec.spl`), `test/01_unit/os/compositor/` (28),
  `test/01_unit/os/services/wm/` (8), `test/01_unit/os/desktop/` (9).
- **Harness mode A (use this everywhere):** in-process headless, no X, no SDL:
  `HostCompositor.new_headless(Size.wh(w, h))` from
  `os.compositor.host_compositor_entry`, plus `SimpleWindow.headless(w, h)`
  from `std.nogc_sync_mut.io.simple_window`. Canonical model:
  `test/03_system/wm/wm_full_stack_demo_spec.spl` (518 lines) and
  `test/03_system/gui/wm_showcase_session_capture_spec.spl` (168 lines).
- Harness mode B (env capture lane, `SIMPLE_WM_HEADLESS_CAPTURE=1`) is
  **avoided by this plan**: it is the lane blocked by the open bug
  `doc/08_tracking/bug/wm_web_standards_showcase_child_frame_timeout_2026-08-06.md`
  (child styling drops to the interpreter via a `[jit-fallback]` on
  `SimpleWebEngine2DStaticPixelCache.retain_result_for_html`; 180 s handshake
  deadline missed). Do not build new units on that lane until that bug closes.
- Lane gating: file-level comment `# @gui: headless` (21 specs use it). All new
  specs in this plan carry it.
- `slow_it` idiom: plain `it` gets the child runner's 120 s budget; long
  compositor scenarios must use `slow_it` (600 s) — see
  `wm_showcase_session_capture_spec.spl:71`.
- Damage mechanics: `skipped_frame_count` + `had_damage` live in
  `src/os/compositor/host_compositor_core.spl:651,699,1594,1698-1713`;
  `report_damage(x,y,w,h)` is a backend-trait method
  (`compositor_engine2d.spl:351`, `hosted_backend.spl:184`, etc.). **Today only
  unit specs assert them** (`test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl`,
  `engine2d_damage_report_spec.spl`, `test/01_unit/os/desktop/hosted_wm_evidence_spec.spl`).
  No 03_system spec does — Wave 2 closes that.
- MCP `play_wm_*`/`play_ui_*`/`play_sdl2_*` tools exist
  (`src/app/mcp/tool_table.spl:285` etc.) but **zero specs call them**; this
  plan does not depend on them (they need a running MCP server — wrong shape
  for container specs).

### 1.2 Coverage tooling — CORRECTED 2026-08-07: line coverage is NOT confirmed real either, not just branch coverage

**This section originally claimed line coverage was "REAL" and only branch
coverage was inert. A 2026-08-07 empirical re-check disproves the "REAL"
half too — full trace:
`doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`.**
Re-running the exact primitive this section describes —
`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/cov.sdn bin/simple test
--coverage --no-cache <a real branching spec>` — produced only the
`coverage: SIMPLE_COVERAGE set; bypassing test daemon` banner line and **no
`coverage: <path> NN%` line, no artifact at the configured output path, no
line data at all.** The only coverage artifact anywhere in the tree,
`build/coverage/coverage.sdn`, is stale (untouched since 2026-08-02) and
carries a branch-shaped schema with `total_decisions: 0`.

- `SIMPLE_COVERAGE=1` genuinely sets a flag the test-runner client reads
  (`src/compiler_rust/compiler/src/coverage.rs:296-300`;
  `src/app/test_runner_new/test_runner_client.spl:368-398` does print the
  "bypassing test daemon" banner) — that much is confirmed. What is **not**
  confirmed is that anything downstream of that flag actually writes or
  prints per-file coverage data on the spipe/.spl runner path an agent would
  actually invoke. The per-target `coverage: <path> NN% (hit/total lines)`
  line this doc originally cited from `test_runner_single.spl:668-713` did
  not appear in the 2026-08-07 repro.
- Root cause: `save_coverage_data`
  (`src/compiler_rust/driver/src/cli/test_runner/coverage.rs:8`) is called
  from `runner.rs:434`, but the spipe/.spl runner path bypasses that call
  chain entirely (that's what the "bypassing test daemon" banner is
  reporting) — so export never fires for a `.spl` spec run this way,
  regardless of `# @cover` headers being correct.
- Function coverage exists only as a *gate* on line counting
  (`test_runner_single.spl:602-668`), not a separate percentage — this claim
  is unaffected by the correction above (it was never claimed to reproduce
  independently).
- **Branch (decision/condition) coverage is INERT**, as originally stated:
  C probes exist (`src/runtime/runtime_coverage_core.c:127-134`,
  `rt_coverage_decision_probe`/`rt_coverage_condition_probe`) but nothing
  instruments `.spl` under `bin/simple test`, and production MIR lowering
  never calls the coverage-instrumented lowering path at all (JIT/native
  codegen emit zero decision probes — see the bug doc's root-cause list).
  Authoritative bugs:
  `doc/08_tracking/bug/instrumented_statement_coverage_tooling_inert_2026-08-02.md`
  and (this correction, plus the line-coverage finding)
  `doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`.
  The Yes/Yes table in `doc/07_guide/infra/testing/coverage.md:30-35` is
  aspirational. `bin/simple doc-coverage` is DOCUMENTATION coverage — never
  cite it as code coverage.
- **Consequence (repo standing rule "measure the primitive first" — this is a
  live example of that rule firing on this very plan's own §1.2)**: U1.3 is
  no longer "resolve the branch-coverage question, line coverage already
  works" — it is now **the single prerequisite unit that must build a working
  measurement primitive (line AND branch) before U1.2's baseline numbers or
  ANY wave-4 closure unit's percentage can be trusted.** Until U1.3 lands and
  is independently reproduced (artifact exists, non-empty, parses), every
  report in this campaign writes `line_coverage=unconfirmed`,
  `branch_coverage=unavailable(pending-U1.3)` — never a fabricated %, and
  never citing a "bypassing test daemon" banner alone as evidence of a
  working measurement.

### 1.3 Container / headless reality
- **`scripts/local-container-test.shs` DOES NOT EXIST** (rules
  `.claude/rules/testing.md:51-52` and
  `doc/07_guide/infra/testing/container_testing.md:200-243` are stale). What
  exists: `tools/docker/Dockerfile.test-isolation` (ubuntu:24.04, entrypoint
  `/opt/simple/bin/release/simple`) and the CI recipe in
  `.github/workflows/containerized-tests.yml:95-102` (docker, `--read-only`,
  `--cap-drop=ALL`, memory/cpu caps, `-v $(pwd):/workspace:ro`).
- Headless GUI in-repo is Xvfb-based only for the *daemon GUI adapter*
  (`src/app/test_daemon/adapters/gui_adapter.spl:114-270`) — NOT needed for
  this plan: harness mode A (`HostCompositor.new_headless`) renders in-process
  with no display server at all. No `SDL_VIDEODRIVER` reader exists anywhere
  in `src/`; do not invent one.
- Coverage runs write `build/coverage/**`, so the read-only CI mount cannot be
  used verbatim for coverage lanes; U1.1 defines the writable-overlay variant.

### 1.4 Browser engine — implemented HTML/CSS surface (the "analysis" deliverable)

Root: `src/lib/gc_async_mut/gpu/browser_engine/` (162 files). Style struct:
`simple_web_html_layout_renderer_foundation.spl` (~461 fields). Property
parsing: `_declarations.spl` / `_decl_apply.spl` / `style_block*.spl`. Layout:
`_layout.spl` / `_core.spl`; paint: `_paint_layout.spl` / `_paint_primitives.spl`.

**HTML elements recognized (tag-match verified):**
a abbr address area article audio b base blockquote body br button canvas
caption center code col dd details div dl em embed fieldset figure footer
h1–h6 head header hr html i iframe img input kbd label legend li link main
mark menu meta meter nav object ol p pre progress samp script section select
selectedcontent slot small source span strong style sub summary sup table
tbody td template textarea tfoot th thead time title tr track ul var video wbr.
Special layout/render behaviour: table family, replaced
(img/canvas/video/iframe/embed/object), form widgets
(input/textarea/select/button/progress/meter/label/fieldset/legend), br/wbr/hr,
list markers (li/ol/ul), pre, details/summary; script/style/template/head/
meta/link/title non-rendered. UA-default styles cover only a subset
(open bug `browser_engine_missing_ua_defaults_2026-07-11.md`).

**CSS properties by cluster — status column drives Wave 3 units:**

| Cluster | Implemented | Missing / partial | Wave-3 unit |
|---|---|---|---|
| Box model | display, width/height, min/max-(width|height), inline/block-size, margin×4, padding×4, box-sizing, aspect-ratio, inset, overflow(-x/-y), resize | `display: flow-root/inline-flex/inline-grid` absent | U3.1 |
| Positioning | position, top/right/bottom/left, z-index, clear, clip | **float unimplemented** (open bug `browser_engine_css_float_layout_unimplemented_2026-07-20.md`; `layout_float.spl` exists, unwired) | U3.7 |
| Flex | flex(+grow/shrink/basis/direction/wrap/flow), justify-content, align-(items/self/content), order, gap/row-gap/column-gap, place-(items/content) | — | U3.2 |
| Grid | grid, grid-template-columns/rows, grid-column/row (fixed track lists) | grid-template-areas, grid-auto-flow, grid-auto-rows, columns/column-count | U3.3 |
| Text | font(+family/size/weight/style/variant), line-height, letter/word-spacing, text-align/decoration/transform/indent/overflow/shadow, white-space, word-break, overflow-wrap, vertical-align, direction, unicode-bidi, list-style(-type) | writing-mode shallow (4–8 hits) | U3.4 |
| Background/border | background(+color/image/size/position/repeat/clip/attachment), border shorthand + per-side, border-radius (8 corners), outline(+offset), box-shadow, filter, border-collapse/spacing | backdrop-filter parsed, **no consumer**; transform/transition/animation shallow | U3.5 |
| Visibility/containment | visibility, opacity, content-visibility, contain (layout/paint/style — `containment.spl`, landed 2026-08-06), pointer-events, will-change, cursor | `contain: size` deliberately out of scope; **contain has ZERO test coverage today** | U3.6 |
| Table/replaced/forms | table display values, table-layout, caption-side, object-fit/position | **table row horizontal layout / table-layout:fixed** (open bug `browser_engine_table_row_horizontal_layout_2026-07-11.md`) | U3.8 |
| Not present at all | — | clip-path, mix-blend-mode, isolation, scroll-behavior, appearance, ruby | RED specs in owning cluster unit + bug filing (see per-unit notes) |

Existing browser-engine tests: `test/01_unit/browser_engine/**` (~25 specs:
tokenizer/tree-builder/table/ifc/text painter/dom), `test/02_integration/rendering/`
(cascade, vars, iframe DrawIR), `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
`test/03_system/check/html_css_full_rendering_goal_status_spec.spl`.
Traceability gate: `scripts/check/check-html-css-sspec-traceability.shs`.

## 2. Requirement IDs minted by this plan

`REQ-WM-SYS-001..005` (Wave 2, one per unit), `REQ-WEB-CSS-001..008` (Wave 3),
`REQ-COV-UI-001..003` (Wave 1 measurement + Wave 4 closure). Put them in
`# @req` comments exactly as spelled here.

## 3. Standard recipes (referenced by every unit)

### 3.1 Container invocation (the ONLY sanctioned commands)

Build image once per checkout SHA:
```bash
docker build -f tools/docker/Dockerfile.test-isolation -t simple-test-isolation:local .
```
Run one spec, hermetic (functional lanes):
```bash
docker run --rm -v "$(pwd)":/workspace:ro --read-only \
  --tmpfs /tmp:rw,size=512m --memory=1g --cpus=2.0 --cap-drop=ALL \
  -w /workspace simple-test-isolation:local \
  test test/03_system/wm/<spec>.spl --no-session-daemon --sequential
```
Run one spec with coverage (writable lane — coverage writes `build/coverage/`):
```bash
docker run --rm -v "$(pwd)":/workspace:rw \
  --tmpfs /tmp:rw,size=512m --memory=2g --cpus=2.0 --cap-drop=ALL \
  -e SIMPLE_COVERAGE=1 -w /workspace simple-test-isolation:local \
  test <spec>.spl --no-session-daemon --sequential 2>&1 | tail -40
```
Rules: NEVER run `test <dir>` in parallel (shared test DB, F2); one spec per
container invocation; verdict = final `Results: N total, ...` line ONLY (F3);
capture output to a file and `tail` it — never pipe to `head`.

### 3.2 Coverage measurement (line, the real primitive)
```bash
SIMPLE_COVERAGE=1 bin/simple test <spec.spl> 2>&1 | tee /tmp/cov_run.txt | tail -40
grep '^coverage: ' /tmp/cov_run.txt
```
Requires `# @cover src/...` header lines in the spec (first 30 lines). Expect
the `bypassing test daemon` banner; if absent, the run measured nothing — fail
the unit's done-check.

### 3.3 Binary provenance (state in every unit's evidence)
```bash
readlink -f bin/simple && bin/simple --version 2>&1 | head -3
```
A seed banner or stale mtime ⇒ evidence applies to the SEED; re-run on the
self-hosted binary or say so explicitly. Record `md5sum $(readlink -f bin/simple)`.

### 3.4 Sabotage protocol (every correctness claim)
In a scratch worktree (`git worktree add /tmp/claude-1000/sab_<unit> HEAD`),
apply the unit's named sabotage edit to the IMPLEMENTATION (never to a shim or
the spec), rerun the spec, require RED with the expected assertion text, then
`git worktree remove --force` it. A sabotage that stays green voids the unit.

### 3.5 Modern SSpec skeleton (copy for every new spec)
```spl
# @cover src/os/compositor/host_compositor_core.spl
# @req REQ-WM-SYS-001
# @gui: headless
"""
<user-voice manual docstring per .claude/templates/spipe_template.spl>
"""
use std.spec.*
use os.compositor.host_compositor_entry
# @manual_section "Window lifecycle"
describe "..." """...""":
    slow_it "creates, moves, resizes and closes a window with correct damage":
        step("Create a 640x600 headless compositor")
        val comp = HostCompositor.new_headless(Size.wh(640, 600))
        ...
        assert_true(...)
```
Matchers: `to_equal/to_contain/...`; bare bools via `assert_true`/`assert_false`
(`to_be_true` is REJECTED). Evidence: print `key=value` receipt lines
(checksums, counters) exactly like `wm_showcase_session_capture_spec.spl`.

### 3.6 Pixel/layout oracles (sanctioned, reuse — do not invent)
- Blank-frame detector: count distinct colors in the `[u32]` frame; require > 2.
- Change detector: frame checksum before/after an action must differ (and must
  NOT differ for a no-op — always assert both directions).
- Region probe: sample a pixel inside a rect painted with a pinned color
  (e.g. `0xFFFFA000u32`) and count occurrences.
- Layout oracle: `common.ui.layout.{compute_layout, find_rect}` for GUI trees;
  for web, walk the `DrawIrComposition` from
  `simple_web_layout_render_html_draw_ir(html, w, h)` and assert command
  rects/colors (DrawIR-tree oracle — preferred for wave 3 because it is
  engine2d-independent, respecting the §0 boundary).

## 4. Waves and units

Dependency DAG (**corrected 2026-08-07**: U1.3 now precedes U1.2, not the
reverse — see U1.3's reframing and
`doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`):
U1.1 → (all wave 2+3 container done-checks). **U1.3 → U1.2 → wave 4** (U1.3
must land or formally park BOTH line and branch measurement before U1.2's
baseline table is trustworthy, and before any wave-4 unit reports a
percentage). Wave 2 and wave 3 units are mutually independent (parallelizable,
one agent each) and do NOT depend on the coverage chain — they can start
immediately. Wave 4 after its module's wave-2/3 units land AND U1.3/U1.2.
Each unit = one agent, one commit, pushed immediately (standing rule), guards
+ ls-remote every time.

---

### Wave 1 — measurement + harness primitives

#### U1.1 Container harness: create `scripts/local-container-test.shs` and prove a WM spec green in it
- **Goal:** make the documented-but-missing script real, prove
  `test/03_system/wm/wm_full_stack_demo_spec.spl` passes inside the container.
- **Files:** NEW `scripts/local-container-test.shs`. NO other files.
- **Behaviour (exact):** POSIX sh. Modes:
  - `unit` → loops a fixed list of smoke specs (start with
    `test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl`)
    sequentially, one `docker run` each (hermetic recipe §3.1).
  - `quick <spec.spl>` → single hermetic run of that spec.
  - `cov <spec.spl>` → single writable coverage run (§3.1 coverage variant).
  - Auto-builds `simple-test-isolation:local` if the image is missing.
  - Exit code = docker run's exit code; last line printed verbatim must be the
    inner `Results:` line (F3) or `ERROR — no results line` with exit 2
    (fail-closed, per repo guard convention).
- **Sketch:**
```sh
#!/bin/sh
set -eu
IMG=simple-test-isolation:local
docker image inspect "$IMG" >/dev/null 2>&1 || \
  docker build -f tools/docker/Dockerfile.test-isolation -t "$IMG" .
run_one() { # $1=spec $2=rw|ro $3=cov|"" 
  MNT="$(pwd):/workspace:ro"; EXTRA="--read-only"; ENVV=""
  [ "$2" = rw ] && { MNT="$(pwd):/workspace:rw"; EXTRA=""; }
  [ "$3" = cov ] && ENVV="-e SIMPLE_COVERAGE=1"
  OUT=$(docker run --rm -v "$MNT" $EXTRA --tmpfs /tmp:rw,size=512m \
    --memory=2g --cpus=2.0 --cap-drop=ALL $ENVV -w /workspace "$IMG" \
    test "$1" --no-session-daemon --sequential 2>&1) ; RC=$?
  echo "$OUT" | tail -60
  echo "$OUT" | grep -E '^Results: [0-9]+ total' >/dev/null || { echo "ERROR — no results line"; exit 2; }
  return $RC
}
case "${1:-}" in
  quick) run_one "$2" ro "" ;;
  cov)   run_one "$2" rw cov ;;
  unit)  run_one test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl ro "" ;;
  *) echo "usage: $0 unit|quick <spec>|cov <spec>"; exit 2 ;;
esac
```
- **Commands:**
  `sh scripts/local-container-test.shs quick test/03_system/wm/wm_full_stack_demo_spec.spl`
- **Sabotage:** point `quick` at a spec with a deliberately wrong oracle
  (temp copy under `/tmp/claude-1000/` with `to_equal(999)`); the script must
  exit non-zero and show the failure — proves the exit code propagates.
- **Done checklist:** [ ] image builds; [ ] wm_full_stack_demo green in
  container with `Results:` line quoted; [ ] wrong-oracle sabotage exits
  non-zero; [ ] `cov` mode shows `bypassing test daemon` + `coverage:` lines;
  [ ] provenance recorded (§3.3); [ ] committed+pushed.
- **Collision set:** `scripts/local-container-test.shs` (new; nothing else
  writes it). **Deps:** none.
- **Risk note:** the container binary is `bin/release/simple` baked at image
  build (see Dockerfile) — rebuild the image after any bootstrap redeploy, and
  record the image's binary md5 in evidence.

#### U1.2 Coverage baseline for the three module families — BLOCKED ON U1.3, reordered
- **Reframed 2026-08-07**: this unit originally assumed the §3.2 `coverage:`
  line reliably appears and only needed running. A 2026-08-07 repro of the
  exact §3.2 command produced no `coverage:` line at all (see
  `doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`)
  — so **U1.2 now DEPENDS ON U1.3 landing a working export first**, reversing
  the original "U1.2 host baseline, U1.3 branch bonus" ordering implied by
  their numbering. Do not start U1.2's baseline table until U1.3's acceptance
  probe (a 10-line fixture reporting real coverage data) passes.
- **Goal:** measured (not guessed) line-coverage baseline for
  `src/os/compositor/**`, `src/lib/gc_async_mut/gpu/browser_engine/**` (layout/
  style/paint core files only — net/, js/, script/ excluded from this campaign),
  and `src/lib/common/ui/**`.
- **Files:** NEW `doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`
  (this report IS requested — the directive is a coverage campaign). NEW dir
  `doc/09_report/ui/testing/` (depth 4, ok).
- **Method (exact):** for each module family pick the 5 highest-value existing
  specs (compositor: the 3 damage unit specs + `wm_full_stack_demo_spec.spl` +
  `hosted_wm_evidence_spec.spl`; browser_engine: cascade + table_layout +
  ifc_linebox + margin_collapse + `simple_web_browser_production_hardening_spec.spl`;
  common/ui: pick by `grep -l "use common.ui" test/01_unit -r | head -5`). Add
  a temporary `# @cover` header ONLY if missing — commit such header additions
  as part of this unit. Run §3.2 per spec SEQUENTIALLY, **first confirm a
  `coverage:` line actually appears at all (it did not, pre-U1.3, on
  2026-08-07)**, then record every `coverage:` line verbatim into the baseline
  doc, one table per family, plus a `branch_coverage=unavailable(pending-U1.3)`
  banner. If a run produces the "bypassing test daemon" banner but no
  `coverage:` line, record that explicitly as `line_coverage=unconfirmed` for
  that spec rather than silently omitting the row.
- **Sabotage:** run one spec with the `# @cover` target misspelled — the
  coverage line must NOT appear (proves lines are per-declared-target, not
  invented). This sabotage is only meaningful once the POSITIVE case (correct
  target → real coverage line) is independently confirmed first.
- **Done checklist:** [ ] ≥15 coverage lines recorded verbatim (not banners);
  [ ] daemon-bypass banner confirmed each run; [ ] misspelled-target sabotage
  documented; [ ] provenance recorded; [ ] committed+pushed.
- **Collision set:** the new report file; any spec files that gain a `# @cover`
  header (list them in the commit message). **Deps: U1.3 (reversed from the
  original "none" — the primitive must work before it can be baselined).**

#### U1.3 Coverage measurement primitive (line AND branch): wire or formally park — THE prerequisite unit blocking U1.2 and all of Wave 4
- **Reframed 2026-08-07, scope widened**: originally titled/scoped as
  "branch-coverage primitive," implying line coverage was already solid and
  only branch needed this treatment. A 2026-08-07 repro disproved that: the
  exact §3.2 line-coverage command produced no `coverage:` line at all, only
  the "bypassing test daemon" banner — see
  `doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`
  for the full trace (production MIR lowering never reaches the
  coverage-instrumented path; decision probes hardcode `"<source>"` file
  identity and `line=0,column=0`; export never fires on the spipe/.spl runner
  path — `save_coverage_data` at `driver/src/cli/test_runner/coverage.rs:8`
  is called from `runner.rs:434`, which this path bypasses). **This unit must
  now confirm or build the LINE-coverage export path before attempting the
  branch-coverage wiring below** — a branch primitive built on top of an
  unconfirmed line-coverage export inherits the same "bypassing" gap.
- **Goal:** resolve the coverage-measurement question honestly, for both line
  and branch. Timebox: one agent session per axis (two sessions total if both
  need building). Two allowed outcomes per axis, decided by a probe, no third
  option:
  1. **Wire it (preferred):** for line coverage, trace why
     `test_runner_single.spl:668-713`'s `coverage: <path> NN%` line did not
     print in the 2026-08-07 repro (check whether `runner.rs:434`'s
     `save_coverage_data` call is actually reachable from the spipe/.spl
     runner entrypoint, or whether a different, disconnected code path needs
     the same wiring) and fix the disconnect. For branch coverage, make the
     interpreter test lane call
     `rt_coverage_decision_probe`/`rt_coverage_condition_probe`
     (`src/runtime/runtime_coverage_core.c:127-134`) for `if`/`match` arms of
     `# @cover` targets, and extend `test_runner_single.spl:668` to print
     `coverage-branch: <path> NN% (hit/total decisions)`. Start from the seed
     interpreter statement-hook sites already used for line coverage
     (`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:530`).
     Acceptance probes: (a) line — a 10-line fixture spec run through the
     real `bin/simple test <spec>` command must produce a `coverage: <path>
     NN%` line AND a non-empty artifact on disk, not just the banner;
     (b) branch — a 10-line fixture spec with one `if` taken one way must
     report `1/2 decisions`.
  2. **Park it (if wiring exceeds the timebox), per axis independently:**
     update
     `doc/08_tracking/bug/instrumented_statement_coverage_tooling_inert_2026-08-02.md`
     and/or `doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`
     with the exact blocker found, and adopt the campaign-wide proxy for
     branch: **enumerated-branch tables** — each wave-4 unit lists every
     `if`/`match` arm of its module (via `grep -n "if \|match \|elif \|else"
     <file>`) in a table `branch → covering it-block`, and "branch coverage"
     for this campaign means that table has no empty rows. If line coverage
     itself must be parked too, the campaign-wide proxy for line is: cite
     only the `# @gui: headless` / `# @req` traceability of which functions
     have a covering `it` at all (existence, not percentage) and label every
     report `line_coverage=unconfirmed`. All campaign reports then say
     `branch_coverage=enumerated-proxy` and/or `line_coverage=unconfirmed`,
     never a fabricated %.
- **Files:** outcome 1: `src/compiler_rust/compiler/src/coverage.rs`,
  `.../driver/src/cli/test_runner/coverage.rs`, `.../runner.rs`,
  `.../interpreter_call/core/function_exec.rs`,
  `src/app/test_runner_new/test_runner_single.spl`, fixture specs
  `test/01_unit/infra/coverage_line_probe_spec.spl` (new),
  `test/01_unit/infra/coverage_branch_probe_spec.spl` (new). Outcome 2: the
  bug doc(s) only. (Outcome 1 touches Rust seed — allowed here because
  coverage collection already lives in the seed; note "Fix .spl not Rust"
  applies to product code, not the seed's own collector.)
- **Sabotage (outcome 1):** line — comment out the export call → the fixture
  must report no artifact / non-green, not a false "bypassing" pass; branch —
  flip the fixture's `if` so both arms execute → must report `2/2`; comment
  the probe call → must report `0/2` not green.
- **Done checklist:** [ ] line-probe fixture verdict quoted (artifact exists,
  non-empty, real `coverage:` line, not just banner); [ ] branch-probe fixture
  verdict quoted; [ ] outcome recorded in the baseline doc from U1.2 (edit its
  banner — note U1.2 now depends on this unit, not the reverse); [ ] both bug
  docs updated with final status; [ ] committed+pushed. **Collision set:**
  listed files; coordinate with any session touching `test_runner_single.spl`
  or the render_2d sibling plan's Unit B1 (same underlying primitive — check
  `git log -1 --format=%ci` + `git status` on shared Rust files first, and
  grep the render_2d plan's B1 section for "IN PROGRESS" before duplicating
  work). **Deps:** none (this is the root prerequisite; nothing in either
  plan's coverage wave should start before this lands or is formally parked).

---

### Wave 2 — WM system sspec units

All wave-2 specs: NEW files in `test/03_system/wm/` (currently 1 file; +5 = 6,
under the 10-file cap). Common harness: §3.5 skeleton, harness mode A,
`# @cover src/os/compositor/host_compositor_core.spl` (plus per-unit extras),
oracles from §3.6. Container done-check for every unit:
`sh scripts/local-container-test.shs quick test/03_system/wm/<spec>.spl`
(host run first; container run after U1.1 lands). Model spec to imitate for
structure: `wm_full_stack_demo_spec.spl`; for oracles:
`wm_showcase_session_capture_spec.spl`.

#### U2.1 `wm_window_lifecycle_system_spec.spl` — REQ-WM-SYS-001
`it` blocks (exact names):
1. `"creates a window and the frame gains its pixels"` — create compositor
   640×600, add window w/ pinned fill `0xFFFFA000u32`, present, region probe
   counts > 0, distinct_colors > 2.
2. `"moves a window and damage follows it"` — move +100,+50; checksum changes;
   old region loses the pinned color, new region gains it; `had_damage` true
   for the frame.
3. `"resizes a window and content re-lays-out"` — resize to 300×200; pinned
   color count changes consistently with area; no crash on 1×1 minimum.
4. `"closes a window and its pixels disappear"` — close; pinned color count
   drops to 0; checksum differs from pre-close (reuses the proven sabotage
   oracle from `wm_showcase_session_capture_spec.spl`).
5. `"a no-op frame after close skips presentation"` — present twice with no
   changes; `skipped_frame_count` increments (bridge to U2.3).
- **Sabotage:** in scratch worktree, stub `report_damage` in
  `src/os/compositor/compositor_engine2d.spl:351` to a no-op → blocks 2 and 5
  must go RED.
- **Done:** [ ] 5 its green host; [ ] green in container; [ ] sabotage RED with
  quoted assertion; [ ] `Results:` line quoted; [ ] provenance; [ ] pushed.
- **Collision set:** the new spec file only. **Deps:** U1.1 for container check.

#### U2.2 `wm_focus_zorder_system_spec.spl` — REQ-WM-SYS-002
`it` blocks:
1. `"clicking a background window raises and focuses it"` — two overlapping
   windows, distinct pinned colors; click via
   `os.compositor.host_gui_event_router` at a point covered by both; the
   clicked window's color now owns the overlap region pixel.
2. `"focused window receives keyboard events, unfocused does not"` — route a
   key event; assert only the focused window's client saw it (use
   `common.io.window_event` receipt as in `wm_full_stack_demo_spec.spl`).
3. `"z-order is stable across a damage-only redraw"` — mark damage on the
   lower window; overlap pixel still belongs to the upper one.
4. `"closing the focused window passes focus to the next in z-order"`.
- **Sabotage:** invert the raise ordering in the compositor's window-list
  reordering (find via `grep -n "raise\|to_front\|z_order" src/os/compositor/host_compositor_core.spl`)
  → 1 and 3 RED.
- **Done/collision/deps:** as U2.1; extra `# @cover src/os/compositor/host_gui_event_router.spl`.

#### U2.3 `wm_damage_present_skip_system_spec.spl` — REQ-WM-SYS-003
Promotes this session's landed present-skip mechanics
(`host_compositor_core.spl:1698-1713`) to system level. `it` blocks:
1. `"a frame with reported damage presents and clears had_damage"`.
2. `"a frame with no damage is skipped and skipped_frame_count increments"`.
3. `"damage in one window does not force redraw pixels of another"` — checksum
   of the untouched window's content-rect is byte-identical across the present
   (byte-identical content-rect oracle already proven in
   `wm_showcase_session_capture_spec.spl`).
4. `"skipped_frame_count stops incrementing once damage arrives"`.
- **Sabotage:** force `had_damage = true` unconditionally at
  `host_compositor_core.spl:1698` region → 2 and 4 RED. Then the inverse
  (force false) → 1 RED. Both directions required.
- **Done/collision/deps:** as U2.1.

#### U2.4 `wm_input_routing_system_spec.spl` — REQ-WM-SYS-004
`it` blocks:
1. `"desktop coordinates translate to client coordinates through the router"`
   (reuse the exact step pattern from `wm_full_stack_demo_spec.spl`'s
   focus-the-text-field scenario).
2. `"clicks outside every window hit the desktop, not a client"`.
3. `"a moved window receives clicks at its new position and not its old one"`.
4. `"pointer-events pass through a window region marked non-interactive"` —
   only if the compositor exposes it; probe first with
   `grep -n "pointer_events\|hit_test" src/os/compositor/*.spl`; if absent,
   write the spec RED + file
   `doc/08_tracking/bug/wm_hit_test_pointer_events_missing_2026-08.md`.
- **Sabotage:** offset the router's coordinate translation by +1 → 1 and 3 RED.
- **Done/collision/deps:** as U2.2.

#### U2.5 `wm_multi_window_scenarios_system_spec.spl` — REQ-WM-SYS-005
`it` blocks (all `slow_it`):
1. `"eight windows tile without pixel bleed between content rects"` — 8 windows,
   8 pinned colors, per-rect region probes exact.
2. `"rapid create/close of 20 windows leaves a clean desktop"` — final frame
   distinct_colors returns to the desktop baseline; no counter leaks
   (`skipped_frame_count` monotone, window list empty).
3. `"overlap chains render in creation order then in raise order"`.
4. `"resize storms coalesce damage without dropping the final geometry"` — 10
   resizes in one frame; final region probe matches last geometry.
- **Sabotage:** as U2.1's report_damage stub → 4 RED.
- **Done/collision/deps:** as U2.1.

---

### Wave 3 — GUI/web HTML/CSS system sspec units

All wave-3 specs: NEW dir `test/03_system/gui/web_css/` (8 files, under cap;
avoids inflating `test/03_system/gui/` past its 83). Common harness — NO
compositor, NO capture lane (dodges the open showcase bug): call
`simple_web_layout_render_html_draw_ir(html, w, h)` from
`use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer` and
assert on the returned `DrawIrComposition` (rect positions/sizes/colors of its
commands) — the DrawIR-tree oracle, §3.6. Where a pixel is truly needed
(gradients, shadows), use `simple_web_html_engine2d_presenter` readback, but
prefer DrawIR. Every spec: `# @gui: headless`,
`# @cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
plus the per-unit file, `# @req REQ-WEB-CSS-00N`. Fixtures: HTML inline in the
spec as text vals — pin colors as hex so DrawIR color assertions are exact.
Container check per unit via U1.1 `quick`. First agent to land also updates
`scripts/check/check-html-css-sspec-traceability.shs`'s expectations if it
enumerates spec files (probe with `head -60` before assuming; if it is
list-based, add your file — collision set includes it for ALL wave-3 units,
so wave-3 agents touch it one at a time, rebase-before-push).

Per-unit `it` blocks (names exact; ~6 each; each block asserts positive AND
negative — e.g. margin applied ⇒ sibling rect shifted AND parent width intact):

#### U3.1 `web_css_box_model_spec.spl` — REQ-WEB-CSS-001
1. `"margins offset a block from its parent and siblings"`
2. `"padding grows the painted background but not the content box"`
3. `"box-sizing: border-box keeps the outer width fixed"`
4. `"min- and max-width clamp an over- and under-sized block"`
5. `"overflow: hidden clips a child's DrawIR to the parent rect"`
6. `"aspect-ratio derives height from width"`
- Sabotage: in scratch worktree zero out padding application in
  `_decl_apply.spl` (find `"padding"` arm) → 2,3 RED.

#### U3.2 `web_css_flex_spec.spl` — REQ-WEB-CSS-002
1. `"row flex places three items left-to-right with gap"`
2. `"flex-grow distributes leftover space proportionally"`
3. `"justify-content: space-between pins first and last items"`
4. `"align-items: center centers cross-axis rects"`
5. `"flex-wrap wraps onto a second line at the container edge"`
6. `"order reorders paint without reordering the DOM"`
- Sabotage: neutralize flex-grow distribution (grep `flex_grow` in
  `_layout.spl`) → 2 RED.

#### U3.3 `web_css_grid_spec.spl` — REQ-WEB-CSS-003
1. `"fixed pixel tracks position cells exactly"`
2. `"fr tracks split remaining space"`
3. `"grid-column spans move a cell across tracks"`
4. `"gap separates tracks in both axes"`
5. RED-by-design: `"grid-template-areas places named cells"` — expected RED
   (unimplemented); leave RED and file
   `doc/08_tracking/bug/browser_engine_grid_template_areas_missing_2026-08.md`
   citing this spec's file:line (testing-rules RED protocol).
6. RED-by-design: `"grid-auto-flow: column fills column-first"` — same bug doc.
- Sabotage (green blocks only): swap row/column track application → 1,3 RED.

#### U3.4 `web_css_text_layout_spec.spl` — REQ-WEB-CSS-004
1. `"text-align: center centers a line's inline boxes"`
2. `"line-height spaces stacked lines by the specified amount"`
3. `"white-space: pre preserves runs of spaces and newlines"`
4. `"overflow-wrap breaks a long unbreakable word at the container edge"`
5. `"text-transform: uppercase changes glyphs not layout width class"` (assert
   via text-run content in DrawIR text commands)
6. `"text-overflow: ellipsis truncates a single-line overflowing box"`
- Sabotage: pin text-align resolution to `left` in `_decl_apply.spl` → 1 RED.
- Note the packed-scene trap: a text run with `painted=N` counts commands
  visited, not glyphs — assert on run glyph/content fields, never `painted`.

#### U3.5 `web_css_background_border_spec.spl` — REQ-WEB-CSS-005
1. `"background-color fills exactly the padding box"`
2. `"per-side border widths and colors paint four distinct edges"`
3. `"border-radius rounds corners (pixel oracle: corner pixel outside radius is background)"` — presenter readback allowed here
4. `"box-shadow paints outside the border box"` — presenter readback
5. `"outline paints outside without affecting layout"` (sibling rect unmoved)
6. `"background-position and -size place an image region"` (DrawIR image cmd)
- Sabotage: drop border-radius corner handling in
  `simple_web_css_box_effects.spl` → 3 RED.

#### U3.6 `web_css_visibility_containment_spec.spl` — REQ-WEB-CSS-006
Closes the **contain zero-coverage gap** (landed 2026-08-06 wiring:
`containment.spl`, `_layout.spl:986`, `_paint_layout.spl:1391`).
1. `"visibility: hidden suppresses paint but keeps layout space"`
2. `"display: none removes both paint and layout space"`
3. `"opacity: 0 still lays out and hit-area remains"`
4. `"contain: layout isolates a subtree's layout from outside changes"` —
   render twice, outer sibling mutated; contained subtree rects identical.
5. `"contain: paint clips descendants to the container"` (fast path at
   `_paint_layout.spl:1391` actually taken — assert clipped DrawIR)
6. `"content-visibility: hidden skips subtree rendering"`
7. RED-by-design: `"contain: size sizes the box independent of content"` —
   documented out of scope in `containment.spl` header; leave RED, reference
   that header in the bug filing.
- Sabotage: make `contain` parse to none in `containment.spl` token fn → 4,5 RED.
- Extra `# @cover src/lib/gc_async_mut/gpu/browser_engine/containment.spl`.

#### U3.7 `web_css_positioning_spec.spl` — REQ-WEB-CSS-007
1. `"position: relative offsets paint without moving siblings"`
2. `"position: absolute anchors to the nearest positioned ancestor"`
3. `"position: fixed anchors to the viewport"`
4. `"z-index reorders overlapping positioned boxes"`
5. `"clear moves a block below preceding content"`
6. RED-by-design: `"float: left takes a box out of flow with text wrap"` —
   open bug `browser_engine_css_float_layout_unimplemented_2026-07-20.md`;
   leave RED, append this spec's file:line to that existing bug doc (do NOT
   open a duplicate).
- Sabotage: zero the relative offset application → 1 RED.

#### U3.8 `web_css_table_replaced_forms_spec.spl` — REQ-WEB-CSS-008
1. `"a 2x2 table places cells in a grid with border-spacing"`
2. RED-by-design: `"table-layout: fixed distributes columns by first row"` —
   open bug `browser_engine_table_row_horizontal_layout_2026-07-11.md`; append
   file:line there.
3. `"img with width/height reserves the replaced box"`
4. `"object-fit: contain letterboxes an image in its box"`
5. `"button and input render intrinsic widget boxes"`
6. `"iframe embeds a child DrawIR subtree at its rect"` (integration precedent:
   `test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl`)
- Sabotage: break border-spacing application in table layout → 1 RED.

---

### Wave 4 — coverage closure (after U1.3 AND U1.2 land or formally park, and the module's wave-2/3 units)

**Gate, not a formality**: do not start Wave 4 until U1.3's done-checklist
shows either a working artifact-producing measurement (outcome 1) or a
formally parked proxy (outcome 2) for BOTH line and branch — see
`doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`.
Every unit below that cites §3.2's `coverage:` line must first confirm that
line actually appears for its target (it did not, pre-U1.3, on 2026-08-07);
if U1.3 parked line coverage too, substitute the enumerated-proxy / existence
citation defined in U1.3 outcome 2 and label the report accordingly — never
report a percentage derived from a "bypassing test daemon" banner alone.

Method for every unit, executable verbatim:
1. Re-run §3.2 with the unit's spec set (sequentially) and record the fresh
   `coverage: <path> NN%` lines. If no such line appears, STOP — U1.3 has not
   actually landed a working line-coverage export for this target; do not
   proceed to step 2 with a banner-only "pass."
2. Produce the uncovered-line list: coverage collector output is line-keyed;
   diff hit-lines against `grep -n "" <target> | wc -l` per function region
   (function regions via `grep -n "^fn \|^    fn \|^  fn " <target>`); list
   uncovered FUNCTIONS by name in the unit's working notes.
3. Write targeted unit specs under `test/01_unit/...` (locations below) named
   `<module>_coverage_closure_spec.spl`, one `it` per uncovered function
   cluster, real oracles (return-value or state assertions — a call without an
   assertion does not count; sabotage one closed function per unit to prove it).
4. Branch reporting per U1.3's outcome: real `coverage-branch:` lines, or the
   enumerated-branch table with no empty rows.
5. Acceptance = the measured line % ≥ target below, quoted verbatim in the
   commit message; update `doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`
   in place (append a "closure" column).

| Unit | Module (exact @cover targets) | Spec location | Line target | Justified exclusions |
|---|---|---|---|---|
| U4.1 | `src/os/compositor/host_compositor_core.spl` | `test/01_unit/os/compositor/` (28→29 files: over the 10/dir doc rule? test dirs are exempt — the ≤10 rule is for doc/; keep flat) | ≥95% | none — pure logic |
| U4.2 | `.../host_gui_event_router.spl` + `hosted_backend.spl` | same dir | ≥90% | SDL2/winit/win32 backend files EXCLUDED (FFI+platform; covered by evidence scripts, not unit-coverable headlessly) — state this in the report |
| U4.3 | `browser_engine/simple_web_html_layout_renderer_style.spl` + `_declarations.spl` + `style_block*.spl` | `test/01_unit/browser_engine/` | ≥95% | none |
| U4.4 | `_layout.spl` + `_core.spl` + `containment.spl` | same | ≥90% | float codepaths (unimplemented, bug-linked) |
| U4.5 | `_paint_layout.spl` + `_paint_primitives.spl` | same | ≥85% | GPU-tile paths (`_paint_tiles_gpu.spl` excluded — sibling plan's territory per §0) |
| U4.6 | `src/lib/common/ui/layout/*.spl` + `wm_app_process_contract.spl` | `test/01_unit/ui/` (create if absent) | ≥95% | none |

**Honesty rules for wave 4:** "almost 100% function/branch" is delivered as:
(a) function — every function in scope appears in the collector's `functions`
section during the closure run (that IS the repo's function-coverage
primitive); (b) branch — per U1.3 outcome, never a made-up %. Modules with
justified exclusions state them in the report; a target miss is reported as a
miss with the blocking defect filed, never quietly rounded up. Historic
100%-claims in `doc/10_metrics/coverage/*` predate the 2026-08-04 line-key fix
— never cite them.

---

## 5. Standing conventions (binding for every executing agent)

- **Sabotage-test every correctness claim** — implementation, not shim
  (`reference_sabotage_the_implementation_not_the_shim`); both directions where
  the oracle is an equality.
- **Binary provenance in every evidence block** — §3.3; container runs record
  the image's baked binary too.
- **Shared working tree:** plumbing-add ONLY your unit's files with a fixed
  private index path (§6); `git diff --stat` review before push; run all 3
  guards; `ls-remote` verify after push; never `git add -A`/whole-WC commits.
- **Sequential test-DB access:** never parallel `simple test <dir>`;
  single-spec targets only; `--no-session-daemon --sequential` in containers.
- **Interpreter-vs-JIT divergence:** `bin/simple test` = tree-walk interpreter;
  `bin/simple run` = Cranelift JIT; they disagree on 18/49 builtins. All specs
  in this plan run under `test`. Never A/B with `SIMPLE_NO_JIT` (decoy); the
  knob is `SIMPLE_EXECUTION_MODE`.
- **F1 workaround:** prefer pass-by-parameter for mutable state in spec
  helpers; avoid module-level `var` mutated across `it` blocks.
- **Native-dict pitfalls:** never `Dict.len()`; never `.get()` on
  struct/class/enum-valued dicts (use `contains_key` + `d[k]`).
- **Verdict discipline:** only the final `Results: N total, ...` line counts;
  capture to file, read the tail; take `$?` from the command, not a pipe.
- **RED protocol:** a correct spec that fails stays RED + bug doc with
  file:line + unblock condition (units U2.4-4, U3.3-5/6, U3.6-7, U3.7-6,
  U3.8-2 pre-authorize this).
- **Push each unit immediately** after its done-checklist — one commit per
  unit, not batched.

## 6. Landing procedure (every unit, verbatim)

```bash
cd /home/ormastes/dev/pub/simple
git fetch origin main -q
BASE=$(git rev-parse origin/main)
IDX=/tmp/claude-1000/idx_wmgui_<unitid>          # unique per unit
GIT_INDEX_FILE=$IDX git read-tree $BASE
GIT_INDEX_FILE=$IDX git update-index --add <exact file list for the unit>
TREE=$(GIT_INDEX_FILE=$IDX git write-tree)
NEWCOMMIT=$(git commit-tree $TREE -p $BASE -F /tmp/claude-1000/msg_wmgui_<unitid>.txt)
git diff --stat $BASE $NEWCOMMIT                  # review: ONLY your files
unset GIT_INDEX_FILE
sh scripts/check/check-no-conflict-tree-push.shs $BASE..$NEWCOMMIT
sh scripts/check/check-no-conflict-markers-push.shs $BASE..$NEWCOMMIT
sh scripts/check/check-tree-size-push.shs $BASE..$NEWCOMMIT
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git push git@github.com:ormastes/simple.git $NEWCOMMIT:refs/heads/main
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git ls-remote git@github.com:ormastes/simple.git refs/heads/main   # must equal $NEWCOMMIT
```
On rejection: re-fetch; confirm your $NEWCOMMIT's parent is an ancestor of the
new origin/main; collision-check YOUR paths against the new tip
(`git diff --name-only $BASE origin/main -- <your paths>` — if non-empty, read
both sides before rebuilding); rebuild the commit on the new base; re-run all
three guards; re-push. Guard verdict grammar: `PASS`/`FAIL`/`ERROR — nothing
was checked` (exit 2 = do not push).

## 7. Global collision registry

| Path | Units writing it |
|---|---|
| `scripts/local-container-test.shs` | U1.1 only |
| `doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md` | U1.2 creates; U1.3 + all U4.x append (serialize: rebase-before-push) |
| `test/03_system/wm/*.spl` | one file per U2.x, disjoint |
| `test/03_system/gui/web_css/*.spl` | one file per U3.x, disjoint |
| `scripts/check/check-html-css-sspec-traceability.shs` | any U3.x IF it is list-based (probe first); serialize |
| `test_runner_single.spl` + seed coverage files | U1.3 only; check for concurrent sessions first |
| Existing bug docs (float, table-row) | U3.7 / U3.8 append file:line refs |
| `test/01_unit/**_coverage_closure_spec.spl` | one per U4.x, disjoint |

Sibling-plan collision: none by construction (this plan never touches
engine2d/paint-kernel/Vulkan files); if the sibling adds specs under
`test/03_system/gui/`, filenames differ (`render_2d_*`/`vulkan_*` prefix vs
`web_css_*`/`wm_*` here).
