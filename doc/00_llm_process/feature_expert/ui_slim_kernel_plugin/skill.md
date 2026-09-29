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

Research/design/plan done 2026-09-05; Wave 1 landed the same day on the seed lane (diagnostic): `screen.spl` single-cell hline batching (`screen_row_copy_count` oracle, 40→1), `shared_wm_route.spl` split (async_app closure 343→9 files), `ui/composition_adapter.spl` (`admit_static`), and `scripts/check/check-ui-slim-closure.shs` (fail-closed, `--selftest`). Gate usage: `sh scripts/check/check-ui-slim-closure.shs src/app/ui.tui/async_app.spl src/os/compositor src/os/drivers src/os/kernel src/lib/skia src/lib/gc_async_mut/gpu`. Caveat: seed `deps fast` resolves package-rooted imports only — a lower bound. Instrumentation: `screen_row_copy_count` (screen.spl) is an always-on module `var` bumped in `_screen_replace_row`; per the log-retention convention it stays as a diagnostic hook and must be gated or removed after Wave 3 certification. Blockers: no certified baseline on macOS (bootstrap shim), Tiny files owned by the open `tiny_ui_web_wm` lane, `kernel_plugin` layer absent, 800-module cap not redeployed. Do not repeat dynSMF default-on, SIMD-first, or a TUI rewrite.

## Wave 2 state (2026-09-06)

`simple ui tui` now runs `run_async_tui` (stub only under `SIMPLE_UI_TUI_STUB=1`; shared-WM TUI via backend key `tui_shared_wm`). `UISession.submit_widget_draw_ir` lives in `ui/session_draw_ir.spl` — GUI/browser callers must `use nogc_sync_mut.ui.session_draw_ir.{}`; a missing import fails loudly. Tiny: `resolved_panes` is linear with bounded per-parent metadata (`metadata_valid()`, `child_ordinal_of`), `tiny_tui_render_into` reuses a caller-owned buffer, `fill_clipped` uses `_fill_span`. Diagnostic counters (all module `var`s, gate/remove after Wave 3): `screen_row_copy_count`, `tiny_cell_buffer_alloc_count`, `tiny_software_*_count`, the layout step counter, `event_wait` wake counter.

## Harness and reference lanes (2026-09-06)

- Startup: `sh scripts/check/check-ui-slim-startup.shs --binary <bin> --lane H0|T0|T1` (guide `doc/07_guide/ui/ui_slim_startup_harness.md`). Pack inventory: `sh scripts/check/check-ui-slim-pack-inventory.shs <entries...>` (`config/ui/pack_prefixes.sdn`). GUI presentation: `sh scripts/check/check-ui-slim-gui-present.shs` (needs `build/sffi/libspl_winit.dylib` + `DYLD_LIBRARY_PATH`; uses the 2026-07-25 stage4 binary).
- References under `test/05_perf/ui_slim/ref/`: termbox2, ncursesw (T1, PTY via expect), microui, Nuklear (widget-core headless), FLTK (`unsupported` until installed). Vendored sources are external code (CLAUDE.md).
- All numbers are `diagnostic` until a deployed pure-Simple `ui` exists; never compare a seed-interpreted Simple run against the C fixtures as a result.

## Seed-lane facts that shape specs here (2026-09-05)

- `thread_spawn`/`thread_spawn_with_args` run their closure synchronously under the seed interpreter; `run()` loops cannot be exercised live on this lane — model arrival-over-time instead.
- Channel `recv()` has an internal 30 s timeout (`channels.rs:124`); `recv_timeout` is NOT exposed as a facade (`src/lib/nogc_sync_mut/concurrent/channel.spl`). Do not add a raw extern in `src/app/`.
- `build_tree_from_source` never returns `Err`; the "parse error keeps old tree" branch is only reachable via file-not-found.
- The closure gate ERRORs on `async_app.spl` and `host_gui.spl` because `deps fast` ignores bare tier-rooted imports — blocker 0b in the plan; a PASS there needs the deps resolver fixed or imports rewritten as `std.`-rooted (not done: mass import rewriting is not a perf change).

## Gate wiring (2026-09-06)

The guard-wiring scan (`check-guard-wiring.shs`) counts mentions in COMMENTS, so wiring guard A can make a guard B named in A's header newly "reachable" and stale its row in `scripts/check/guard_wiring_unwired_baseline.txt` — expect that cascade and fix the row in the same change.

## Update Checklist

- Add links to requirements, specs, reports as waves land.
- Record Tiny ownership transfer in both lane state files before any Tiny edit.
- Refresh blockers ledger and this file after each pipeline stage.
