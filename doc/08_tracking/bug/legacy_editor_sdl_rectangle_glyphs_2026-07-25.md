# Legacy editor SDL rectangle glyphs
## Closed 2026-09-16 — fixed in source; Draw IR bridge + regression spec; runtime confirmation pending

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** Fixed in source; runtime confirmation pending a refreshed self-host.

## Symptom

`gui_sdl_render_text_block` painted every non-space character as the same
filled rectangle, so the legacy editor SDL host did not use selected fonts or
the shared bitmap fallback.

## Root cause and fix

The bridge owned a private placeholder raster path. It now resolves font
metrics in the GUI producer, emits a `DrawIrComposition`, lowers that through
the canonical Engine2D Draw IR executor, and only converts the final ARGB
readback to SDL's packed RGBA format.

## Regression

`test/03_system/gui/editor_gui_sdl_spec.spl` is a source-contract regression
requiring resolved/shaped Draw IR metadata, Engine2D lowering and shutdown,
zero-skipped-command failure handling, SDL channel conversion, and absence of
the former rectangle helper. Pixel/runtime confirmation remains pending the
refreshed self-host noted above.

