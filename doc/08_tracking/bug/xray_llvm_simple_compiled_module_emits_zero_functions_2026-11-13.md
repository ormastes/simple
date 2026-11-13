# `compile --native --backend=llvm --xray` emits an object with zero functions (2026-11-13)

Status: open. Keeps the real-binary LLVM column of the XRay ("spy") differential
BLOCKED for profile, exclusive fold, container switch and aspect dynload.

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
