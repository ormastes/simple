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
| 1 (smallest useful slice) | A03 screen batching + frame builder; P08 thin TUI route adapter (the `async_app.spl:29` import swap is an A00 integration-window edit, not A03's); old/new differential specs | `src/app/ui.tui/screen.spl`, new `src/app/ui.tui/shared_wm_route.spl` (landed 2026-09-05, 343 → 9 files), `test/01_unit/app/ui/screen_batching_spec.spl` (landed, 11/11), `test/01_unit/app/ui/tui_route_closure_spec.spl` (landed, 2/2) | one-cell parity corpus (ASCII/Korean/combining/wide/ANSI/negative/zero/right-edge); row-copy + alloc counts down; `async_app` closure excludes `os/drivers`,`os/kernel`,`lib/skia` in ordinary mode |
| 1 | A02 composition adapter | `src/lib/nogc_sync_mut/ui/composition_adapter.spl` (dir exists; sync tier chosen to match `composition` — the `nogc_async_mut` default-tier rule is satisfied later by an `export use` wrapper), `test/01_unit/lib/ui/composition_adapter_spec.spl` | static and dynamic routes equivalent; sabotage: duplicate id, wrong ABI, missing interface, release-while-live |
| 1 | A08/A09 references (parallel, no timing overlap) | `test/05_perf/ui_slim/ref/{termbox2,ncursesw,nuklear,microui,fltk}/` | frozen upstream rev + flags; real PTY / real window; closure accounting |
| 2 | A06 event wait/watch | `src/app/ui.tui/async_app.spl` | no lost input/reload; idle wake count; input latency |
| 2 | A04/A05/A07 Tiny layout/render/software | Tiny files — transfer recorded 2026-09-06; **landed** `a63af020` / `a1fdf293` / `ba74a4d4` | geometry/cell/pixel parity proven against in-spec old-route oracles; warmed fixed-scene 0 allocs (A05) |
| 2 | in-process tui dispatch (no tty-inheriting spawn facade: `process_run` pipes, `rt_process_spawn_async` nulls stdin) | `src/app/ui/cli_entry.spl` — landed `7b732fe0`; `_simple_binary()` defined `348dd773` | T1 harness first end-to-end PASS (median 6.8 s, seed-interpreted, diagnostic); cli_entry closure 149 files, 0 forbidden |
| 2 | P08 cont.: session skia split | `src/lib/nogc_sync_mut/ui/session_draw_ir.spl` — landed `7794d60b` | async_app closure skia 20 → 0 |
| 2 | A10 pack closure | pack metadata under `config/ui/packs.sdn` (name to confirm) | required/later/absent inventory; X1 first-use timing |
| 3 | A00 integrate → A01 serialized measurement → A11 certify | reports under `doc/09_report/ui/` | `CERTIFIED` / `PARTIAL_WITH_BLOCKERS` / `REJECTED` |

Do NOT start with: dynSMF default-on, SIMD/GPU kernels, a bottom-up TUI rewrite, a
second registry/loader, or a Tiny edit while the Tiny lane holds the file.

## Blockers (explicit)

0. ~~**`simple ui tui` is a stub**~~ CLOSED 2026-09-06 (`f131dfa0`): the real parser-backed app runs by default; the stub survives only behind `SIMPLE_UI_TUI_STUB=1` for the size audit. Original note: (`doc/08_tracking/bug/ui_tui_cli_entry_is_a_stub_2026-09-05.md`): the parser-backed TUI has no CLI caller, so the closure win on `async_app.spl` does not reach the shipped command until a wiring decision is made (Wave 2, needs owner decision).
0c. **Entry map (measured 2026-09-06 with the fixed deps):** the shipped `simple ui` path is `src/app/ui/cli_entry.spl` (118 files, 0 forbidden; the Rust driver dispatches `ui` there, `main.rs:481`) which spawns `src/app/ui/backend_entry_tui.spl` (114 files, 0 forbidden) as a separate process. `src/app/ui/main.spl` closes over 875 files / 263 forbidden because it imports every backend in-process; it is imported only by `src/app/ui/build.spl` and is NOT on the product path — never use it as a TUI startup measurement. Advisory push rows now gate all three entries.
0b. **`deps fast` ignores bare tier-rooted imports** (`common.X`, `nogc_sync_mut.X`); closure numbers are lower bounds and the gate now ERRORs on unresolved edges instead of passing blind.
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
