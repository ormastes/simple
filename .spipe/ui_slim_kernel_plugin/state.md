# Feature: ui-slim-kernel-plugin

## Raw Request

`/goal with spipe skill, refactor ui to devide to kernel and other. to speed up opening compare with well know library fix perf bugs. check next doc on download folder and copy to reserach folder and research more and make design and plan. however there was research about old try check them too. and check can use kernel/plugin arch used (even with refactoring).`

## Task Type

feature (research → design → plan; implementation waves follow)

## Refined Goal

Split each TUI/GUI product into a composition kernel (existing `nogc_sync_mut.composition` subset), selected providers, and declared feature packs so a minimal TUI/GUI loads only its closure; fix the source-verified work amplification (P01–P11); compare against termbox2/ncursesw/Nuklear/microui/FLTK with a fail-closed harness; preserve every public API and full-product feature.

## Acceptance Criteria

UI-SLIM-001..012 as listed in `doc/01_research/ui/slim_kernel_plugin/simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md` §2, adopted verbatim.

## Scope Exclusions

New grammar, replacement WM, rewriting UI in C, immediate-mode conversion, SOSIX unification, browser replacement, GPU scheduler redesign, building the async `kernel_plugin` layer (owned by the lint plan).

## Runtime Boundary Decision

runtime_need: none new. facade_checked: `std.nogc_sync_mut.composition`, `std.io_runtime`. chosen_path: reuse-facade. rejected_shortcuts: dynSMF default-on (NO-GO), new registry/loader, per-cell FFI.

## Phase

plan-done (research, design, plan written 2026-09-05; implementation Wave 0 not started)

## Phases
- [x] research — `doc/01_research/ui/slim_kernel_plugin/repo_verification_addendum_2026-09-05.md`
- [x] design — `doc/05_design/ui/slim_kernel_plugin/design.md`
- [x] plan — `doc/03_plan/ui/slim_kernel_plugin/plan.md`
- [ ] requirements — `doc/02_requirements/{feature,nfr}/ui_slim_kernel_plugin.md`
- [ ] spec (Wave 1 RED-first)
- [ ] implement
- [ ] verify
- [ ] ship

## Blockers ledger (2026-09-05)

| id | blocker | owner / unblock |
|---|---|---|
| B-1 | macOS `bin/simple` is a bootstrap shim; no certified baseline | deploy pure-Simple full CLI with `ui`; seed lane diagnostic only |
| B-2 | Tiny files (`tiny/gui/state.spl`, `tiny/tui/*`, `tiny/engine2d/software.spl`) owned by open lane `tiny_ui_web_wm` (review FAIL 2026-08-16) | record transfer in both state files before Wave 2 Tiny work |
| B-3 | `nogc_async_mut/kernel_plugin` absent | static composition; consume when lint lane lands it |
| B-4 | 800-module cap fix not redeployed | `SIMPLE_MODULE_LIMIT=4000` / `--no-session-daemon` |

## Knowledge routing

Registry route added (`doc/00_llm_process/knowledge_registry.sdn` feature_routes: `ui_slim_kernel_plugin` → group `rendering_ui`); receipt `.spipe/ui_slim_kernel_plugin/knowledge_selection.sdn`.

## Commits (rebuild the landing from these; WC carries peer-owned conflicts)

- `a2b14405` (change `msmzxovl/0`) — 8 files: addendum+tldr, design+tldr, plan+tldr, state, wiki. `msmzxovl/1` (`57482dff`, 35 files, undescribed) is a PEER reconcile copy sharing the change id — not ours, not abandoned.
- `ae19f34c` — the three imported source documents (blobs `35abc223`, `f264f7cc`, `118bd27b`).
- Landing route: detached worktree at origin sha + PR to `main`; never `jj git push` from this WC (peer conflicts in `doc/03_plan/infra/spipe/spipe_knowledge_compiler_refined_plan.md`, `scripts/check/guard_wiring_optout.txt`).

## Log

- 2026-09-05: imported three Downloads docs; verified R02–R08 at HEAD `56dd3059c2e`; seed `deps fast` closure `async_app.spl`=344 files (drivers/kernel/skia reached), `ui/main.spl`=79, `host_gui.spl`=4 (resolver stops); composition landed (28 callers, 35 specs), kernel_plugin absent; wrote addendum, design, plan, feature wiki.
