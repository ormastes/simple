# `compile --native --backend=llvm --xray` emits an object with zero functions (2026-11-13)

Status: verification-pending (zero-function root cause fixed 2026-11-14; the
`clang_rt.xray` link below is still open). Kept the real-binary LLVM column of
the XRay ("spy") differential BLOCKED for profile, exclusive fold, container
switch and aspect dynload.

## Root cause (2026-11-14) — one cause, not LLVM- or Windows-specific
`cli_compile_pure_simple` (`src/app/io/_CliCompile/compile_opt_and_driver.spl`)
set `options.cli_mode_text = "aot"` only under `xray_enabled and native_target != ""`.
`native_target` is non-empty only via `cli_compile_xray_native`
(`--backend=native --xray`) and only when `cli_xray_native_target` finds a Linux
host or an explicit `--target`. Every other native-output route left
`cli_mode_text == ""`, so in `80.driver/driver_pipeline_lowering.spl`
`native_entry_closure_mir` was false and the per-source gate
(`if native_entry_closure_mir or driver_source_matches_entry(...) or SIMPLE_UNSTUB_HIR`)
replaced the positional source with an empty `MirModule` stub;
`driver_aot_native_output.spl` then emitted `simple_empty_module_<name>`.
That is why Linux `--backend=native --xray` had functions while Linux
`--backend=llvm --xray`, and every backend on Windows (with or without `--xray`,
`pub` or not, `main` or not), had none. No path-separator, visibility,
reachability or seed-interpreter difference is involved.

Fix: `cli_compile_pure_simple_mode_text(output_format)` returns `"aot"` for
native output (`""`/`"native"`) on every route; non-native formats keep `""`.

Evidence (Windows x64, seed-tip seed, llvm-mingw UCRT clang as `CC`,
`--backend=llvm`, shared): before — `functions_emitted=0`, sole export
`simple_empty_module_test_fixtures_xray_xray_inprocess_prog`; after — exports
`test.fixtures.xray.xray_inprocess_prog.{add1,scaled,traced}` and a Simple host
(`rt_host_dynlib_open` + `rt_call_ptr_2`) reads `traced(1)=44 scaled(0)=7
scaled(5)=15`. Spec: `test/03_system/native/pure_simple_compile_library_functions_spec.spl`.

Not established: the Linux aarch64 LLVM lane was not re-run (the rc=137 OOM
that followed the empty module there is unexplained). On Windows
`--backend=native` now reaches codegen with functions and fails loudly at link
(`ld.lld: ... unknown file type` — no Win64 COFF emitter, separate record)
instead of linking an empty DLL with rc=0.

## Symptom
The pure-Simple CLI entry (`cli_compile`, run under the pinned seed 554460a6b85a,
aarch64) on `test/fixtures/xray/xray_inprocess_prog.spl`, shared-library intent:

    [WARN] non-vacuity: lane_receipt name=native-build verdict=mismatch modules_seen=1
      modules_lowered=1 functions_emitted=0 statics_emitted=0 objects_written=1
      reason=emitted zero functions and zero statics

after which the process is OOM-killed inside an 8 GiB scope (rc=137). The same
source and driver with `--backend=native` build and run (`CLI-COMPILE rc=0`).

## What the LLVM lane still needs after that
`80.driver/driver_xray_link.spl` links the resident runtime only for
`backend == "native"`; an LLVM `--xray` link must add `clang_rt.xray` (present:
`$LLVM/lib/clang/23/lib/aarch64-unknown-linux-gnu/libclang_rt.xray{,-dso}.a`) and
`src/runtime/xray/xray_llvm_adapter_linux.c` (PR4), and the compile-time gate
keeps `TraceBackendV1.Llvm` at UnsupportedProfile until then.

## Resume
    XR_SRC=test/fixtures/xray/xray_inprocess_prog.spl XR_OUT=/tmp/libllvm.so XR_XRAY=1 \
      SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared <seed> run <copy of xray_native_cli_compile_driver.spl with --backend=llvm>
