# Executable Size Reduction Architecture

Codex design, 2026-04-23.

The change stays inside existing build boundaries.

## Native Build Link Layer

`NativeProjectBuilder::link_objects` remains the native link orchestrator. On ELF platforms, `libsimple_native_all.a` now links as a normal archive after adding `-Wl,-u,<symbol>` roots. The root set is computed from generated object undefined symbols intersected with runtime-defined symbols, plus a small explicit list for runtime lifecycle, argument, dispatch, string, and array entrypoints.

`SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` selects the old force-load behavior for diagnostics.

## Release Package Layer

`.github/workflows/release.yml` continues to build native MCP/LSP binaries with the bootstrap runtime, but passes `--strip` and then calls `scripts/check-executable-size-budgets.shs` on package outputs.

## Guardrail Layer

`scripts/check-executable-size-budgets.shs` owns byte budgets and release-strip checks. Budgets are configurable through environment variables so release maintainers can adjust thresholds without editing workflow logic.
