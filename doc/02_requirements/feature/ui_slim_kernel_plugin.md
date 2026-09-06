# Slim UI Kernel/Plugin Feature Requirements

Selected scope: the composition-recipe design in `doc/05_design/ui/slim_kernel_plugin/design.md`
(no option docs were produced; the external design's invariants UI-SLIM-001..012 were
adopted as-is). Plan: `doc/03_plan/ui/slim_kernel_plugin/plan.md`.

## Requirements

| ID | Requirement |
|----|-------------|
| `REQ-UI-SLIM-001` | Existing application-visible widgets, events, themes, layout, clipping, scrolling, keyboard behaviour, and error behaviour remain available after the split. |
| `REQ-UI-SLIM-002` | State authority, TinyPane relationships, TinyDrawStream boundaries, and full-IR adapters are preserved; no competing public UI model or IR. |
| `REQ-UI-SLIM-003` | Provider discovery and admission reuse `std.nogc_sync_mut.composition` (`SimpleProviderQueryV1`); no second loader, manifest language, or provider lifecycle. |
| `REQ-UI-SLIM-004` | A no-watch TUI entry's ordinary-mode closure contains no GUI window, GPU, browser, full compositor, or file watcher; verified by an import/link closure gate, not by log absence. |
| `REQ-UI-SLIM-005` | A GUI entry initializes only its selected presentation path and required text/widgets. |
| `REQ-UI-SLIM-006` | Static products use static composition; dynamic placement is optional per feature. |
| `REQ-UI-SLIM-007` | No-GC and bounded-memory operation are explicit profiles with executable allocation tests. |
| `REQ-UI-SLIM-008` | Every performance claim names executable, build lane, features, platform, cache state, and measurement boundary; a missing measurement is `NOT_MEASURED`. |
| `REQ-UI-SLIM-009` | Loading less never removes a required feature, skips rendering, bypasses validation, or substitutes a headless counter for a visible GUI. |
| `REQ-UI-SLIM-010` | Optimizations preserve value/COW semantics: a private reusable buffer never mutates an earlier published snapshot. |
| `REQ-UI-SLIM-011` | Old and new routes stay differentially testable until parity and performance gates pass. |
| `REQ-UI-SLIM-012` | Optional-feature first-use time and peak memory are measured alongside startup. |

## Evidence

Wave 1 specs: `test/01_unit/app/ui/screen_batching_spec.spl` (010, 011),
`test/01_unit/app/ui/tui_route_closure_spec.spl` (004, 009),
`test/01_unit/lib/ui/composition_adapter_spec.spl` (003, 006),
`scripts/check/check-ui-slim-closure.shs` (004, 005). Later waves per the plan.
