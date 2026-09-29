# Slim UI Kernel/Plugin NFR Requirements

Absolute budgets are frozen only after a certified baseline exists on a deployed
pure-Simple `ui` binary (`doc/03_plan/ui/slim_kernel_plugin/plan.md` § Blockers).
Until then the structural gates below apply; timing rows read `NOT_MEASURED`.

| ID | Requirement |
|----|-------------|
| `NFR-UI-SLIM-001` | Startup comparisons report median, p95, spread, and uncertainty over ≥100 interleaved warm launches on an idle runner; a difference within noise is `INCONCLUSIVE`, never a win. |
| `NFR-UI-SLIM-002` | The ordinary-mode TUI entry closure excludes `src/os/compositor`, `src/os/drivers`, `src/os/kernel`, `src/lib/skia`, and `src/lib/gc_async_mut/gpu`; the gate is fail-closed and self-tested. |
| `NFR-UI-SLIM-003` | For the targeted screen workload, row-table copies and allocations decrease relative to the old route measured in the same tree and binary. |
| `NFR-UI-SLIM-004` | No newly introduced per-cell or per-pixel cross-ABI call; batches carry explicit lengths. |
| `NFR-UI-SLIM-005` | Idle TUI behaviour is event/deadline driven; legitimate timer/platform wakes are counted and reported, not claimed zero. |
| `NFR-UI-SLIM-006` | A warmed fixed minimal scene targets zero steady-state allocations where the resource model permits; every exception is reported. |
