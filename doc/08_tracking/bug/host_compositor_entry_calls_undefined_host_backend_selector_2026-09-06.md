# host_compositor_entry calls `_host_backend_selector`, which is defined nowhere

**Date:** 2026-09-06 · **Status:** OPEN · **Found by:** slim-UI lane (running `test/01_unit/app/ui/shared_wm_entrypoints_spec.spl`)

## Symptom

`os.compositor.host_compositor_entry` references `_host_backend_selector` with no
definition anywhere under `src/` (same defect class as the `_simple_binary()` call in
`src/app/ui/backend_loader.spl`, fixed 2026-09-06). Under the seed the shared-WM
entry-point spec reports 7/8 with `function _host_backend_selector not found`; under
JIT the module is dropped to the interpreter with `unresolved external symbol`.

## Consequence

The shared-WM backend selection path (`run_shared_wm_tui` → `init_host_wm`) cannot
resolve its selector, so the `tui_shared_wm` product entry is dead at that call site.
Not touched by this lane: `src/os/compositor/**` is read-only for it.

## Unblock

Define or restore `_host_backend_selector` in `src/os/compositor/host_compositor_entry.spl`
(check `git log -S'_host_backend_selector'` for the removing commit), ship the
reproducing example (that spec's failing case) plus a generalization spec that greps
every `src/os/compositor` module for called-but-undefined `_`-prefixed helpers, and
re-run `shared_wm_entrypoints_spec` to 8/8.
