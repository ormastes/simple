# Stage4 full-CLI lane: HIR shard workers crash (0xC0000005) + 4 triple-quote parse errors (2026-10-25)

Status: OPEN. Lane abandoned for disk space; evidence below was captured before cleanup.

## Setup
- Compiler: stage2 `simple.exe` built from `wt-rel3-new` @ d72188e68ec (static exe, Windows x86_64-pc-windows-gnu).
- Source: `release/1.0.0` @ 42d00bfe4c9 (run 1) and WA commit 67865301a04 (base b129dc3c2b9, PR #4743) (run 2).
- Command: `native-build --target x86_64-pc-windows-gnu --backend llvm --runtime-bundle core-c-bootstrap --mode one-binary --entry src/app/cli/main.spl --threads 56`,
  env `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_FILE_WORKERS=1 SIMPLE_HIR_SHARD_WORKER_KB=1500000 SIMPLE_PARSE_SHARD_MAX=8 SIMPLE_CACHE_SCOPE=s4mir SIMPLE_LLVM_BIN=/c/msys64/clang64/bin` (plus `build/run-new-env.sh`).

## Bug 1 — HIR shard workers crash, 19/19 failed (stage2 runtime class)
- `[hir-shard] completed_workers=0 failed_workers=19 failed_modules=0 unfinished=-1 ledger=<cache>/default/frontend/queue-30472-0`
- Per-owner statuses: 10 × exit -1073741819 (0xC0000005 access violation; 1 `CRASH`, 9 `BLOCKED`), 8 × `BLOCKED exit=1`; all `claimed=0 sealed=0`.
- Ledger dir held only `BLOCKED`: "incomplete worker or ledger publication".
- Admission line: `estimate=1500000 kB historical parent peak=23484 kB`.
- Stage3 completed 5/5 HIR shards with the same stage2 on a 1495-file closure; the full-CLI closure (2935 files, 18-19 shards) fails — closure/size dependent.
- Spawn site: `src/app/cli/native_build_main.spl:1365` (`process_spawn_async(..., native_file_worker_child_args_v1(args, "--hir-shard={spec}"))`); shard count from `:1259-1262`.
- Fallback not yet tried: `SIMPLE_HIR_SHARDING=0` (in-process lowering).

## Bug 2 — cache scope ignored
`SIMPLE_CACHE_SCOPE=s4mir` was exported, but the cache was written under `<cache>/default/`.

## Bug 3 — 4 parse errors inside multi-line `"""` literals (Stage4 closure only)
Reported after `surface_freeze` as `[ERROR] phase 2 FAILED (4 recorded error(s))`, then `phase=parse state=failed total=2935`:
- `src/os/_QemuRunner/os_build_run.spl:476:80` expected field name after '.' (docstring)
- `src/os/qemu_compiler_admission_v1.spl:13:72` expected field name after '.' (docstring)
- `src/app/devhub/gui.spl:11:1` unexpected token '<' (HTML value literal)
- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl:18:1` "use # for comments" (PTX value literal)

All four have continuation lines at column 0 inside the literal. The same files parse clean through stage2 `compile` standalone (LF-only, identical blobs), so the trigger is the whole-program / shard load path, not the lexer itself. Not in stage3's bootstrap_main closure.
Bisect (SHARD_MAX=1 unmodified vs SHARD_MAX=8 with only the admission docstring indented) was stopped before a verdict. A workaround (`WA-P3-LEX-TRIPLEQ-col0`) was conditionally approved by the reviewer, but only in a form that keeps the string bytes identical and only after the bisect gives a verdict; it has not been applied.
