# Phase 2 native-build of Caret dies with fail-fast after a staged-codegen batch (2026-11-22)

Status: OPEN (compiler defect in the admitted Stage 2 `stage2-admitted/simple.exe`,
pinned source `ac2e90625c2a`). Takes effect only in the next compiler generation; no source
workaround applied.

## Symptom

Windows MSVC, worktree source `release/1.0.0` @ `37d7ba1ba6b`, private cache:

```
native-build --entry src/app/llm_caret/main.spl --backend=llvm --low-memory --mode dynload
  --entry-closure --target x86_64-pc-windows-msvc --runtime-bundle core-c-bootstrap
  --runtime-path <S3>/stage2-runtime-authority --threads 1
env: Stage 3 transcript vector + SIMPLE_MIR_SHARDING=0 SIMPLE_FILE_WORKERS=0
     SIMPLE_BUILD_MEMORY_RESERVE_BYTES=2147483648
```

After 1841 s (closure: 1366 modules), the worker exits `0xC0000409` (fail-fast). The full worker stderr
(`<cache>/diagnostics/native-build-stderr-*-1.log`, 16.7 MB) ends:

```
aot:staged_codegen:batch:start -> aot:lower_to_mir -> mir_verify (8 modules:
  app.llm_caret.{provider,image_profile,multimodal_types,multimodal_provider,tools,types},
  lib.gc_async_mut.slang.model_executor.backend, ...) modules=8 functions=273 fatal=0
invalid pattern: match statement exhausted without matching any pattern (no arm matched); match at line 830
```

The same compiler and env built `src/app/devhub/main.spl` (304 modules) successfully (`devhub.exe`
`--help`/`--version` OK), so the env and runtime authority are sound.

## Analysis so far

Of the `src/compiler/**` files with a `match` at line 830 (parser comment, `35.semantics/resolve.spl`,
`55.borrow/borrow_check/mod.spl`, `90.tools/formatter/main.spl`), the one that plausibly runs after
`mir_verify` is (stdlib files compiled into the binary were not scanned)
`src/compiler/55.borrow/borrow_check/mod.spl:830`, `convert_place`: `match proj:` over
`MirProjection` (`src/compiler/50.mir/mir_instruction_support.spl:136`). That match already
covers all four variants (Deref/Field/Index/Downcast). If this is the failing site, a
`MirProjection` element in `MirPlace.projection` reached the borrow checker with a tag outside
those variants. That would mean a corrupt or mis-decoded enum-in-array value in natively
compiled Stage 2 code, not a missing arm.

Not yet confirmed: which function in that batch carries the bad projection, and whether the
site is in fact borrow_check (the message has no file name). Next step: rebuild with
`SIMPLE_COMPILER_PHASE_PROFILE=1` per-function borrow-check tracing, or bisect the 8-module batch.

## Unblock condition

Identify the producing MIR construct, fix the encode/decode in `src/compiler`, and rebuild
Caret with the next compiler generation. Adding a default arm would hide the corruption
and is not an acceptable workaround.
