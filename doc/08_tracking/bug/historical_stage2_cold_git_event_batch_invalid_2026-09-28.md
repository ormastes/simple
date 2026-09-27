# Historical Stage2 cold Git-event batch fails admission

**Status:** open diagnostic; source defect versus historical Stage2 codegen is
unresolved. This is distinct from the fixed non-source-path filter in
`release_scv_cold_init_event_invalid_non_source_paths_2026-09-16.md`.

## Reproduction

The retained `build/mini_builds/target56_focused_worker/fixture/` is a tiny
committed Git repository with only `src/a.spl` in the source scope. The
`admission_probe` binary was compiled from the current worktree by the
admitted historical Stage2 producer, with `SIMPLE_NO_STUB_FALLBACK=1` and the
core-C runtime. From the fixture directory, run it with an isolated
`SIMPLE_CACHE` ending outside `src/` and
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`. It returns
`observed-event-apply:event-invalid` before publishing an inventory.

Git lists only `H src/a.spl`. A separately compiled `event_inspection`
binary shows that a direct Git event and the event produced by
`compiler_inventory_file_event_v1` both have source `git`, operation
`create`, and identity `src/a.spl`; each passes
`compile_source_inventory_apply_event_v1`. A `cold_array_inspection` binary
passes each as a one-element array through cold replay without the original
`event-invalid`, then fails at publication because its omitted defaulted
cursor arguments do not act as empty values in this historical native binary.

A temporary failure formatter in cold replay caused a segfault on a tagged
value while formatting the rejected row. It was reverted. The original
controlled failure remains; no source fix is admitted from this diagnostic.

## Next proof

Use an admitted current-source compiler and a focused bridge probe with every
cursor argument explicit. Capture the batch returned by
`compiler_inventory_git_events_v1` before passing it through
`compile_source_inventory_apply_observed_events_v1`. Compare its event fields
and array length with the one-event controls. Only then decide whether the
source bridge or the historical compiler needs repair. See
`doc/09_report/compiler/target6_test_worker_build_2026-09-27.md` for logs,
cache locations, and the three-build session cap.
