# Seed `rt_host_dynlib_open` returns 0 for every library (aarch64 Linux, 2026-11-13)

Status: fixed in source (be65da720dd); the deployed seed is stale. Root cause corrected 2026-11-13 — see "Root cause (corrected)" below.

## Symptom
`sh scripts/check/check-xray-native-inprocess-e2e.shs --simple src/compiler_rust/target/bootstrap/simple`
(seed dated 2026-11-05, aarch64) builds the `--xray` and OFF modules, passes
object/twin inspection, then the in-process host fails:
`FAIL — in-process host did not complete (rc=0): E2E-HOST-ERROR: dlopen/runtime symbols: 10`
(10 = `TraceFailureV1.InvalidArgument`, raised at
`src/lib/nogc_sync_mut/trace/xray_native_module_v1.spl:332` when `rt_host_dynlib_open` returns 0).

## Isolation
- A C probe (`clang`, `dlopen(path, RTLD_NOW)`) opens BOTH kept modules
  (`libon.so`, `liboff.so`) successfully; `llvm-nm -D -u` shows only weak glibc
  symbols; `NEEDED` is libc/libm only. The artifact is fine.
- `simple run` of a two-line program calling the extern directly:
  `rt_host_dynlib_open("libm.so.6", 2)` -> 0, `rt_host_dynlib_open(<liboff.so>, 2)` -> 0.
  The symbol name exists in the seed binary (11 string hits) but the call
  yields 0 for every input — the unregistered-extern silent-nil class
  (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`).

## Impact
`test/03_system/xray/xray_backend_differential_out_spec.spl` (simple describe)
is `@tag:in-development` until a binary built from PR5b or later is deployed.
The IN differential (`test/01_unit/lib/xray/xray_backend_differential_in_spec.spl`)
is unaffected (33/33 on this seed).

## Fix path
Deploy a seed/self-hosted binary that registers `rt_host_dynlib_open`
(bootstrap run-21 or later), re-run the lane; no source change in this lane.

## Root cause (corrected 2026-11-13)
The "unregistered extern" diagnosis above is wrong. The interpreter adapter
(`src/compiler_rust/compiler/src/interpreter_extern/host_dynlib.rs:15`,
registered at `interpreter_extern/mod.rs:289`) has existed since 2026-08-25 and
the same Nov-5 binary opens every library under `SIMPLE_EXECUTION_MODE=interpret`.
The failure is the JIT lowering only: the deployed seed
(`src/compiler_rust/target/bootstrap/simple`, Nov 5 18:12) predates
`be65da720dd` (2026-11-06 14:22), which added `rt_host_dynlib_open => [0]` /
`rt_host_dynlib_symbol => [1]` to the seed `text_arg_indices` tables
(`compiler/src/codegen/instr/calls.rs:3248`, LLVM twin
`codegen/llvm/functions/calls.rs:172`). Without them the JIT passed the boxed
text handle as `path_ptr` and `mode` as `path_len`
(`runtime/src/value/wsffi_native.rs:55`), so `raw_text_cstring` built a
2-byte path and `dlopen` returned 0 — the same defect as
`seed_jit_host_dynlib_open_text_arg_not_split_2026-11-06.md`, seen on aarch64.

## Red -> green (aarch64 Linux, clang-built `libdynprobe.so`)
Gate: `sh scripts/check/check-host-dynlib-open-call.shs <simple-binary>`
(fixture `test/fixtures/compiler/seed_jit_miscompiles/host_dynlib_open_call_symbol.spl`:
dlopen + dlsym + `spl_wffi_call_i64` + dlclose, both engines).
- Nov-5 seed: `jit: open_ok=false sym_ok=false` / `interpret: ... call=1042 close=0` -> FAIL exit 1
- seed built from release/1.0.0 `f9411a43849` (sha256 `f2e4a20f644faeb7…`):
  `jit` and `interpret` both `open_ok=true sym_ok=true call=1042 close=0` -> PASS exit 0
- `cargo test --release -p simple-compiler --test host_dynlib_text_abi_jit`: 4/4 ok
  (incl. `host_dynlib_generated_calls_load_a_real_library` on Linux).

## Twins
C twin `src/runtime/runtime_native.c` `rt_host_dynlib_open/symbol/close` matches
the Rust twin (mode bit 2 -> `RTLD_NOW` else `RTLD_LAZY`, `| RTLD_LOCAL`; 0 on
failure; 1 MiB cap; close(<=0) = -1). One divergence fixed: the C twin silently
truncated a path/name at an embedded NUL while Rust (`CString::new`) fails
closed; C now rejects it too. Pure-Simple lowering table
`src/compiler/50.mir/text_extern_abi.spl:170-172` already splits both names.

## Remaining blocker for the OUT lane (separate defect)
A seed built from current release/1.0.0 carries the interpreter call-time
private-fn gate (`6d15331f91e`, 2026-11-09; `interpreter_call/mod.rs` `gate_private_call`
-> `interpreter_module/module_loader.rs` `check_private_call_visibility`, no env
switch). The lane builds the `--xray` module by INTERPRETING the compiler
(`xray_native_cli_compile_driver.spl`), and cross-directory calls to private
compiler fns that are not in `scripts/check/private_import_baseline.txt` are now
rejected, so the build stops before reaching dlopen:
`semantic: private fn native_compile_result of .../70.backend/backend/native/mod.spl
is not visible to src/plugins/backend_native/native_codegen_adapter.spl`
(marking it `pub` only moves the error to `isel_module_context` in
`backend/common/isel_context.spl` — a chain, not a one-liner). The lane's FAIL
line misreports it as `parser_error(...)` because
`scripts/check/lib/xray-inprocess-e2e-lib.shs:127` greps the first line
containing "error", which is echoed source context.

## XRay in-process host past dlopen (2026-11-13)
Modules built by the Nov-5 seed (lane `--keep`), then:
- host step with the Nov-5 seed: `E2E-HOST-ERROR: dlopen/runtime symbols: 10` (the original red)
- same `libon.so`, host step (`run test/fixtures/xray/xray_native_inprocess_host.spl`)
  with the fresh seed: rc=0, both sessions patch/record/unpatch,
  `records_after_stop=0 lost=0`, `E2E-HOST-OK`.
So the OUT spec's simple column clears dlopen once a current seed is deployed;
it stays `@tag:in-development` until the private-fn visibility chain above is
fixed so the same seed can also BUILD the `--xray` module.
