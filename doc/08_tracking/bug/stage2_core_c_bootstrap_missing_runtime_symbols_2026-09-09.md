# Stage-2 core-C bootstrap is missing runtime symbols

**Date:** 2026-09-09  
**Status:** Resolved on `slang-physical-provider-activation`; Stage-2 now links

## Reproducer

```text
sh scripts/bootstrap/run-phase1-local.shs
```

The original failure occurred after the Stage-2 pure-Simple `native-build`
compiled 861 modules and reached the final link.

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

## Resolution evidence

- `runtime_file_view.c` supplies real descriptor-pinned, beneath-root file
  views and archive capabilities, with an executable traversal/symlink/range
  self-check.
- `runtime_secure_staging.c` supplies the four narrow native-all bootstrap ABI
  gaps without importing collision-heavy `runtime.c`.
- The two `Result[Unit, ...]` call sites now use canonical `Result[(), ...]`.
- `libsimple_native_all.a` contains each formerly missing symbol exactly once.
- The 2026-09-09 Stage-2 build compiled 861/861 modules and linked successfully,
  then advanced to compiler sanity. Its later sanity failure is tracked in
  `stage2_rust_transient_promotion_positional_hello_2026-09-09.md`.
