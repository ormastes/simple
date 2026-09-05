# Feature Expert — Slim UI kernel/plugin

## Role

Own the split of TUI/GUI products into composition kernel + selected providers + declared feature packs, the source-verified perf backlog (P01–P11), and the fail-closed startup/memory comparison against termbox2/ncursesw/Nuklear/microui/FLTK.

## Invariants

- Kernel = existing `std.nogc_sync_mut.composition` subset; no second loader, registry, manifest language, grammar, or UI tree.
- Public UI API, value/COW `Screen` semantics, TinyPane/TinyDrawStream boundaries, stream validation, and receipts are preserved.
- A no-watch TUI hello never initializes GUI/GPU/compositor/watcher; a GUI hello initializes one presentation path.
- Every number names executable, lane, features, platform, cache state; `NOT_MEASURED` is never zero; within-noise is `INCONCLUSIVE`.
- Static composition until dynSMF reopen gates pass; async `kernel_plugin` is consumed, not built here.

## Entry points

- State: `.spipe/ui_slim_kernel_plugin/state.md`
- Research: `doc/01_research/ui/slim_kernel_plugin/` (external design + briefs + prior lint kernel/plugin plan + repo verification addendum)
- Design: `doc/05_design/ui/slim_kernel_plugin/design.md` · Plan: `doc/03_plan/ui/slim_kernel_plugin/plan.md`
- Source owners: `src/app/ui/main.spl`, `src/app/ui.tui/{screen,async_app}.spl`, `src/app/ui_showcase/hosts/host_gui.spl`, `src/lib/nogc_sync_mut/composition/`, `src/lib/nogc_sync_mut/tiny/**` (Tiny lane)
- Related experts: `../tiny_ui_web_wm/skill.md`, `../ui_gui/skill.md`

## Known state

Research/design/plan done 2026-09-05. Blockers: no certified baseline on macOS (bootstrap shim), Tiny files owned by the open `tiny_ui_web_wm` lane, `kernel_plugin` layer absent, 800-module cap not redeployed. Do not repeat dynSMF default-on, SIMD-first, or a TUI rewrite.

## Update Checklist

- Add links to requirements, specs, reports as waves land.
- Record Tiny ownership transfer in both lane state files before any Tiny edit.
- Refresh blockers ledger and this file after each pipeline stage.
