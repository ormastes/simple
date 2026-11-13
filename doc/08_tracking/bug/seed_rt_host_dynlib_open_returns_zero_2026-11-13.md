# Seed `rt_host_dynlib_open` returns 0 for every library (aarch64 Linux, 2026-11-13)

Status: open. Blocks the pure-Simple XRay OUT lane on this host.

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
