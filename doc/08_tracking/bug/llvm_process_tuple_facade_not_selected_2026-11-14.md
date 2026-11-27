# LLVM process tuple facade not selected in admitted P2 probe

Status: fix implemented in source (LLVM backend unit specs passed in interpreter mode; native AArch64 P2 probe re-verification pending). Severity: P1 for effectful compiler/tool subprocess results. Not a claim that every importer or backend is affected.

Producer SHA256: `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`, source `33bc5c6d1d8`. A private Git fixture compiled with native-build, explicit entry closure/cache and `--runtime-bundle core-c`; provider receipt says `backend=llvm`. Compilation exited 0. Executing the exact XRay runtime-materialization helper then failed its archive-query guard (exit 10), although the qualified Clang query works natively.

Disassembly provides the concrete mismatch: `main.process_run_timeout` calls raw `rt_process_run_timeout` with command split into pointer/length, argument array and timeout. Its caller destructures the result by loading offsets 0, 8 and 16 as a tuple. `runtime_native.c` documents that the raw process result is a `SplArray*`, and supplies `rt_process_run_timeout_tuple` to convert it into this native tuple layout. The generated call did not select that facade. The untimed `rt_process_run` in the fixture likewise targets the raw symbol.

Relevant current source: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` selects the timed facade when `args.len() == 4`; inspect whether direct extern logical arguments are counted before physical text expansion. This is a hypothesis, not an accepted root-cause fix. Compare imported production owners before broadening the rewrite.

Reproducer and retained evidence: `/tmp/xray-effectful-next-20261114/failed-raw-process-main.spl.txt`, `compile.log`, `compile.exit` (0), `run.log`, `run.exit` (10), `materialize-probe`, and `cache-effectful/native_provider_identity.receipt`. The program uses real runtime process and secure-temp leaves; there is no mocked successful process response.

A separately labeled fixture may bind the already-existing native tuple facades explicitly to qualify the exact materialization executor. That bypass is test-only and does not fix or qualify the normal compiler-selection/IO-wrapper/CLI path. Keep public LLVM activation gated. Repair acceptance requires a native Simple program using the ordinary process owner, correct stdout/stderr/status for successful and failing commands, and generated-call evidence for the expected facade.

## Fix (2026-11-18)

### Root Cause
- Commit `522524e8c05` consolidated tuple-result facade selection into `runtime_tuple_result_facade` (`src/compiler/50.mir/text_extern_abi.spl`) for `MirCallOrigin.Runtime` and `MirCallOrigin.Foreign`, but `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` (`translate_call_at`) still unconditionally returned `""` whenever `func.call_origin == MirCallOrigin.Source` and passed unstripped `bare_name_for_call` without consulting `self.owned_name_has_local`.
- Direct/cached/imported `extern fn rt_process_run*` calls that reach `translate_call_at` with `MirCallOrigin.Source` (e.g., via default `MirCallOrigin.Source` on projected/rehydrated `MirOperand`s or quoted symbol names) therefore skipped `runtime_tuple_result_facade` (and under non-no-mangle could even be mangled via `llvm_function_symbol_name` to `__simple_local_rt_*`).

### Repair
- Extracted `pub fn llvm_select_runtime_tuple_facade_v1(bare_name: text, arg_count: i64, call_origin: MirCallOrigin, has_local_source_body: bool) -> text` in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`.
- It strips LLVM quotes (`.replace("\"", "")`), delegates to `runtime_tuple_result_facade(normalized_name, arg_count)` (preserving exact runtime names and post-split word counts so 1-arg wasm `rt_process_run` and non-extern module-qualified symbols still return `""`), and suppresses the redirect only when `call_origin == MirCallOrigin.Unknown` or `call_origin == MirCallOrigin.Source and has_local_source_body` (`self.owned_name_has_local.has(...)`).
- Extracted `llvm_is_owned_alias_or_runtime_name_v1` so `translate_module` populates `self.owned_name_has_local` for both `fn_owner.name` and `@export("C", name: "...")` `fn_owner.export_name` (preventing `@export("C", name: "rt_process_run")` local bodies from being rewritten at the post-target fallback).
- Extracted `MirToLlvm.llvm_resolved_tuple_facade_for_call_v1` and wired it into both `translate_call_at` and `CallTerminator` (`translate_terminator_at`) ahead of `translate_call_target_at` (avoiding spurious `@__simple_local_rt_*` declarations), keeping `translate_call_at`'s post-remap fallback on `bare_static_name`.
- Cross-module `--no-mangle` note: ordinary cross-module Simple functions are module-qualified (`<mod>.<fn>`), so they never match exact `rt_*` names; `--no-mangle` (`SIMPLE_NATIVE_BUILD_NO_MANGLE=1`) is reserved for C-ABI runtime provider builds (where `rt_process_run` IS the runtime provider or local `owned_name_has_local` applies in-module). Cranelift (`cranelift_codegen_adapter.spl`) was intentionally kept untouched in this LLVM lane.
- Updated `test/01_unit/compiler/backend/stage4_process_provider_spec.spl` to match the refactored `llvm_select_runtime_tuple_facade_v1` contract and `test/01_unit/compiler/backend/native_runtime_tuple_result_abi_spec.spl` to test local `Source` bodies separately from non-local `MirCallOrigin.Source` projected runtime calls.

### Verification (interpreter mode; no `native-build` run in this lane)
- `test/01_unit/compiler/backend/llvm_process_tuple_facade_origin_spec.spl`: 11 total, 11 passed, 0 failed (pure selector cases plus `MirToLlvm.translate_module` IR tests covering ordinary/`@export("C")`/`--no-mangle` local bodies, non-local `Source` without `__simple_local_rt_*`, quoted names, `CallTerminator`, `MirCallOrigin.Unknown` `E-BACKEND-LLVM-CALL-ORIGIN`, and `Runtime`/`Foreign` with local bodies).
- `test/01_unit/compiler/backend/stage4_process_provider_spec.spl`: 7 total, 7 passed, 0 failed.
- `test/01_unit/compiler/backend/native_runtime_tuple_result_abi_spec.spl`: 7 total, 7 passed, 0 failed.
- `test/01_unit/compiler/backend/runtime_tuple_result_facade_census_spec.spl`: 4 total, 4 passed, 0 failed.
- `sh scripts/check/check-nil-outside-unsafe-added.shs --rank` on `core_codegen.spl`, `llvm_process_tuple_facade_origin_spec.spl`, `stage4_process_provider_spec.spl` (`0` each) and `git diff --check` clean (6 pre-existing `nil`s remain untouched in `native_runtime_tuple_result_abi_spec.spl`, 0 added).
