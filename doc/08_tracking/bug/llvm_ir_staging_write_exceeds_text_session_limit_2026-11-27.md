# LLVM IR staging write fails for modules whose IR exceeds the 16 MiB text-session limit

Status: fix-implemented-verification-pending (needs a stage2 lane whose
compiler-test matrix reaches `compiler_cli_build` serial codegen)

## Symptom

Stage 2 compiler-test matrix, `compiler_cli_build` row (lane v7d, pin
3dd00937c329, 2026-11-27):

```
[native-compile-failed] compiler.mir._MirLoweringExpr.expr_dispatch:
  AOT compile error in compiler.mir._MirLoweringExpr.expr_dispatch:
  Failed to write LLVM IR to private staging
error:   name-len=43 reason-len=42
[build] phase=native_compile state=failed ... failed=1
```

## Root cause

`llvm_object_stage_*` in `src/compiler/70.backend/backend/llvm_backend_tools.spl`
wrote `module.ll` through `std.nogc_sync_mut.io.file_ops.file_write`, whose
`file_session_encode` admits at most `FILE_TEXT_DEFAULT_LIMIT` (16 MiB,
`src/lib/nogc_sync_mut/io/file_text_session.spl:21`) of UTF-8. A large
compiler module's LLVM IR (expr_dispatch is among the biggest) exceeds that,
the encode refuses, and the write reports failure.

The bootstrap lanes never saw this because they export `SIMPLE_BOOTSTRAP=1`,
which selects the unbounded `rt_file_write_text_at` branch. The stage2
compiler-test matrix rows do NOT export `SIMPLE_BOOTSTRAP`, so the capped
branch ran and only the largest module tripped it. Lane v7c never reached
this codegen (row timeout); lane v7d reached it and failed.

## Fix

All four IR-writing sites in `llvm_backend_tools.spl` now use
`file_write_bytes(path, text_to_bytes(ir))` (no text-session cap) instead of
`file_write`:

- `llvm_object_stage` non-bootstrap branch (the failing one)
- the sibling staging writer (`wrote_ir = ...` Err path)
- the wasm temp-IR writer
- the best-effort `kept_ir` diagnostic copy (a large IR is exactly the one
  worth keeping)

## Verification

- Pending: next stage2 lane's `compiler_cli_build` row must compile
  `compiler.mir._MirLoweringExpr.expr_dispatch` past the staging write.
- The failure is deterministic given IR > 16 MiB and no SIMPLE_BOOTSTRAP=1;
  the v7d log above is the reproducer.
