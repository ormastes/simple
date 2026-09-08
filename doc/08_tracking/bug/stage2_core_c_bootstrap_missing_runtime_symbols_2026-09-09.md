# Stage-2 core-C bootstrap is missing runtime symbols

**Date:** 2026-09-09  
**Status:** Open; blocks admitted-runtime verification for the physical paged-KV lane

## Reproducer

```text
sh scripts/bootstrap/run-phase1-local.shs
```

The Rust seed and runtime prerequisites complete. The Stage-2 pure-Simple
`native-build` compiles 861 modules, then the final link fails.

## Observed linker gap

The `core-c-bootstrap` command links `libsimple_native_all.a`, but the selected
runtime authority does not define 15 required runtime APIs, including
`rt_file_create_excl`, `rt_file_sync`, `rt_simple_abi_version`, the
`rt_file_view_*_v1` family, and the `rt_pinned_archive_*_v1` family. A separate
frontend/lowering defect emits an unresolved global named `Unit` from functions
returning `Result[Unit, ...]`.

Evidence is retained at:

```text
.simple/storage/build/bootstrap/logs/aarch64-unknown-linux-gnu/stage2-native-build.log
```

## Required acceptance

- Provide real, non-duplicating implementations for every selected runtime ABI
  or exclude unreachable dependents from the Stage-2 entry closure.
- Lower `Unit()` results without emitting an external `Unit` symbol.
- Complete Stage-2 admission and emit the sanity/provenance receipts.
- Regenerate the changed SPipe manuals and run compiler/lib/MCP checks with the
  admitted pure-Simple runtime.

Fake compatibility stubs and Rust-seed verification do not satisfy this gate.
