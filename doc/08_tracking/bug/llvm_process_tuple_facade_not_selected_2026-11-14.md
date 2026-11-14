# LLVM process tuple facade not selected in admitted P2 probe

Status: open; reproduced on Linux AArch64. Severity: P1 for effectful compiler/tool subprocess results. Not a claim that every importer or backend is affected.

Producer SHA256: `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`, source `33bc5c6d1d8`. A private Git fixture compiled with native-build, explicit entry closure/cache and `--runtime-bundle core-c`; provider receipt says `backend=llvm`. Compilation exited 0. Executing the exact XRay runtime-materialization helper then failed its archive-query guard (exit 10), although the qualified Clang query works natively.

Disassembly provides the concrete mismatch: `main.process_run_timeout` calls raw `rt_process_run_timeout` with command split into pointer/length, argument array and timeout. Its caller destructures the result by loading offsets 0, 8 and 16 as a tuple. `runtime_native.c` documents that the raw process result is a `SplArray*`, and supplies `rt_process_run_timeout_tuple` to convert it into this native tuple layout. The generated call did not select that facade. The untimed `rt_process_run` in the fixture likewise targets the raw symbol.

Relevant current source: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` selects the timed facade when `args.len() == 4`; inspect whether direct extern logical arguments are counted before physical text expansion. This is a hypothesis, not an accepted root-cause fix. Compare imported production owners before broadening the rewrite.

Reproducer and retained evidence: `/tmp/xray-effectful-next-20261114/failed-raw-process-main.spl.txt`, `compile.log`, `compile.exit` (0), `run.log`, `run.exit` (10), `materialize-probe`, and `cache-effectful/native_provider_identity.receipt`. The program uses real runtime process and secure-temp leaves; there is no mocked successful process response.

A separately labeled fixture may bind the already-existing native tuple facades explicitly to qualify the exact materialization executor. That bypass is test-only and does not fix or qualify the normal compiler-selection/IO-wrapper/CLI path. Keep public LLVM activation gated. Repair acceptance requires a native Simple program using the ordinary process owner, correct stdout/stderr/status for successful and failing commands, and generated-call evidence for the expected facade.
