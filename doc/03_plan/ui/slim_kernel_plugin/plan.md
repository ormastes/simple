# Slim TUI/GUI kernel/plugin — implementation plan

**Date:** 2026-09-05 · **Base:** HEAD `56dd3059c2e` · **Status:** PROPOSED
**Design:** `doc/05_design/ui/slim_kernel_plugin/design.md`
**Research:** `doc/01_research/ui/slim_kernel_plugin/`
**Lane:** `.spipe/ui_slim_kernel_plugin/state.md`
**Agent briefs (external, adapted below):** `doc/01_research/ui/slim_kernel_plugin/simple_slim_ui_parallel_agent_briefs_2026-09-05.md`

## Acceptance

UI-SLIM-001..012 from the external design are the acceptance IDs; every spec cites one
as `# @req REQ-UI-SLIM-NNN`. Definition of done: a real minimal TUI and a real minimal
GUI run through preserved APIs; their closures are documented and verified by link/map
evidence; full products keep tested behaviour; before/after startup and memory exist for
pinned artifacts. Differences within noise are `INCONCLUSIVE`, never wins.

## Repo-rule translations of the external process

| External | This repo |
|---|---|
| `perf/ui-slim/*` branches | no branches: detached worktree at the origin sha + PR to `main` (memory: shared jj WC absorbs edits; verify `jj diff -r @- --stat`) |
| "two reviewers" | highest-capability review gate after sidecar work (spipe skill) |
| Phase-0 baseline on current binary | BLOCKED on macOS (`bin/simple` = bootstrap shim); seed lane = diagnostic; certified numbers need a deployed pure-Simple `ui` |
| Linux `/proc`, `ldd`, xvfb harness | macOS rows via `otool -L`, `/usr/bin/time -l`, `vmmap`, else `unsupported`; template cells stay `NOT_MEASURED` |
| Tiny files owned by A04/A05/A07 | owned by open lane `tiny_ui_web_wm` (review FAIL) — Wave 2 needs an explicit transfer recorded in both state files |
| A10 SMF pack placement | static composition until dynSMF reopen gates pass (`doc/03_plan/ui/perf/smf_default_ui_caching_plan.md`) |
| heavy-UI `simple test` runs | `SIMPLE_MODULE_LIMIT=4000` or `--no-session-daemon` until the 4000 cap is redeployed |

## Waves

| Wave | Package | Owned paths | Evidence gate |
|---|---|---|---|
| 0 | A00 ledger + A01 harness | `.spipe/ui_slim_kernel_plugin/`, `test/helpers/ui_slim/`, `test/05_perf/ui_slim/` (`test/05_perf/` exists), `scripts/check/check-ui-slim-closure.shs` | harness rejects blank GUI, TUI/GUI mislabel, stale binary, concurrent build; closure gate reads link map/`deps`, not log absence |
| 1 (smallest useful slice) | A03 screen batching + frame builder; P08 thin TUI route adapter (the `async_app.spl:29` import swap is an A00 integration-window edit, not A03's); old/new differential specs | `src/app/ui.tui/screen.spl`, new `src/app/ui.tui/route_adapter.spl`, `test/01_unit/app/ui/screen_batching_spec.spl` | one-cell parity corpus (ASCII/Korean/combining/wide/ANSI/negative/zero/right-edge); row-copy + alloc counts down; `async_app` closure excludes `os/drivers`,`os/kernel`,`lib/skia` in ordinary mode |
| 1 | A02 composition adapter | `src/lib/nogc_sync_mut/ui/composition_adapter.spl` (dir exists; sync tier chosen to match `composition` — the `nogc_async_mut` default-tier rule is satisfied later by an `export use` wrapper), `test/01_unit/lib/ui/composition_adapter_spec.spl` | static and dynamic routes equivalent; sabotage: duplicate id, wrong ABI, missing interface, release-while-live |
| 1 | A08/A09 references (parallel, no timing overlap) | `test/05_perf/ui_slim/ref/{termbox2,ncursesw,nuklear,microui,fltk}/` | frozen upstream rev + flags; real PTY / real window; closure accounting |
| 2 | A06 event wait/watch | `src/app/ui.tui/async_app.spl` | no lost input/reload; idle wake count; input latency |
| 2 | A04/A05/A07 Tiny layout/render/software | Tiny files — **after transfer from `tiny_ui_web_wm`** | geometry/cell/pixel parity; warmed fixed-scene zero allocs or accounted |
| 2 | A10 pack closure | pack metadata under `config/ui/packs.sdn` (name to confirm) | required/later/absent inventory; X1 first-use timing |
| 3 | A00 integrate → A01 serialized measurement → A11 certify | reports under `doc/09_report/ui/` | `CERTIFIED` / `PARTIAL_WITH_BLOCKERS` / `REJECTED` |

Do NOT start with: dynSMF default-on, SIMD/GPU kernels, a bottom-up TUI rewrite, a
second registry/loader, or a Tiny edit while the Tiny lane holds the file.

## Blockers (explicit)

1. Baseline binary on macOS — needs deployed pure-Simple `ui`; until then all numbers are seed-lane diagnostic.
2. Tiny file ownership — `tiny_ui_web_wm` lane open with FAIL review.
3. Async kernel_plugin layer absent — static composition only; do not stub it.
4. 800-module cap not redeployed — workaround env above.

## Next spipe phase

Requirements docs (`doc/02_requirements/{feature,nfr}/ui_slim_kernel_plugin.md`) and the
Wave 0 ledger; then Wave 1 specs written RED first (reproduce-first), then code.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.plan -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.plan hash=sha256:auto render=ascii
@layout dag
@direction LR

W0_ledger_harness -> W1_screen_batching
W0_ledger_harness -> W1_route_adapter
W0_ledger_harness -> W1_composition_adapter
W0_ledger_harness -> W1_c_references
W1_screen_batching -> W2_event_wait
W1_composition_adapter -> W2_pack_closure
tiny_lane_transfer -> W2_tiny
W2_event_wait -> W3_integrate_measure_certify
W2_pack_closure -> W3_integrate_measure_certify
W2_tiny -> W3_integrate_measure_certify
W1_c_references -> W3_integrate_measure_certify
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.plan hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
