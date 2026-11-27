# Natively linked CUDA program: rt_cuda_init never opens libcuda, so init returns cuda-init-failed

- **Date:** 2026-11-22
- **Status:** verified 2026-11-26 (authority built with feature `cuda`; see Resolution)
- **Severity:** P2. A natively built CUDA program cannot initialize the driver on a
  live CUDA host.
- **Found by:** lane `work/cuda-compiler-bugs`, while verifying
  `native_build_entry_closure_collects_zero_files_cuda_fill_probe_2026-08-19`.
- **Owner:** CUDA runtime/extern lane. This is a runtime fault, not a compiler one.
- **Related:** `native_c_runtime_missing_cuda_provider_forwarders_2026-11-22`
  covers the link failure seen without `--runtime-path`: 28 `rt_cuda_*` externs
  have no C forwarder. This record covers the case where linking succeeds.

## Repro

Host: Linux aarch64 with a live NVIDIA GB10;
`/usr/lib/aarch64-linux-gnu/libcuda.so.1` (580.173.02) is present.

```
<stage2> native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/processing_cuda_fill_probe.spl --strip \
  --runtime-path <stage2-runtime-authority> --output <bin>
PROCESSING_CUDA_FILL_PROBE_BIN=<bin> sh scripts/check/check-processing-cuda-fill-native.shs
```

- Stage 2: integ25 (sha256 `ef46f0d2...`). The build exits 0; binary sha256 prefix
  `d23f4ff9137083ce`.
- Probe output: `PROCESSING_CUDA_NATIVE status=fail reason=cuda-init-failed ...`
  and `processing_cuda_fill_native_status=fail reason=probe-failed`.

## Evidence
- `strace -f -e trace=openat` of the probe: no libcuda open is attempted. The
  only `.so` opens are libc, libm, libgcc_s, libicu* and liblzma.
- `strings <bin> | grep -i libcuda` finds nothing.
- The authority archive's `rt_cuda_init` object (`libsimple_native_all.a`,
  `simple_runtime` cgu.06) does reference `dlopen`. So either a different
  definition wins at link time, or the driver path comes from a provider
  configuration that the probe does not set: `SIMPLE_CUDA_PROVIDER_PATH` and
  `SIMPLE_CUDA_PROVIDER_SHA256`, per the related record. This was not tried here.

## Next step
1. Find out which `rt_cuda_init` the probe link resolves; the link-command file
   sits next to the output.
2. Re-run the probe with a provider configured (`build/sffi/libsimple_gpu_cuda.so`
   plus the env above).
3. If no provider is configured, the probe should report device-absence instead
   of `cuda-init-failed`. Decide whether that is the intended contract.

## Root cause (2026-11-26, work/bug-cuda-native-20261126)

1. **Ownership.** With `--runtime-path <stage2-runtime-authority>`, the authority's
   Rust `simple_runtime::cuda_runtime::rt_cuda_init` wins the link. In the
   probe, `nm` places it at 0x240a28, and it disassembles to
   `OnceLock<CUDA_INIT_RESULT>::get_or_init(init_cuda)`. The authority is built
   without feature `cuda`, so it returns `NotInitialized` (3).
   native-all compiles `runtime_dynload.c` with `SIMPLE_GPU_PROVIDER_REGISTRY_ONLY`,
   which removes every `GPU_CALL` forwarder, so nothing consults
   `SIMPLE_CUDA_PROVIDER_PATH`. strace shows no provider open and no libcuda open,
   and the binary carries no libcuda or `cuInit` strings. This matches the
   evidence above.
   - Repro: `src/app/test/cuda_device_query_probe.spl` built with
     `--runtime-path` prints `init=3` even with the provider set.
   - Built without `--runtime-path` (core-C forwarders), the same probe reports
     `NVIDIA GB10 capability=121`.
2. **Provider not loadable (fixed).** Even through the core-C forwarders, the
   provider (`libsimple_runtime.so`, feature `cuda`) failed `dlopen` with
   `cannot allocate memory in static TLS block`. Initial-exec TLS in
   `runtime_timestamp.c` made the DSO `DF_STATIC_TLS`. The Rust crate now
   defines `SIMPLE_RUNTIME_DYNAMIC_TLS`.

Decision needed (Rust/native-all lane owner), one of:
- (a) the non-cuda Rust twins defer to the C provider registry;
- (b) the native-all archive stops defining `rt_cuda_*` so the C forwarders own
  them, as `config.rs`'s host-gpu comment already intends;
- (c) the authority is built with `cuda`.

Without a provider, init=3 is the existing cross-lane contract.

## Resolution (2026-11-26), verified on GB10

The owner picked option (c): the stage2 runtime authority is built with `cuda`.

- **Fix.** `src/compiler_rust/native_all/Cargo.toml` adds `cuda` to
  simple-runtime's features. That is the archive the authority publishes
  (`libsimple_native_all.a`, built by `bootstrap-from-scratch.sh`
  `rust-native-all-build` and by every other native-all lane). The pin in
  `check-bootstrap-portability.shs` is updated to match.
- **No link dependency on CUDA.** The `cuda` feature needs no SDK. The driver is
  `libloading`-dlopen'ed at run time.
- **Proof** (integ25 Stage 2 `ef46f0d2…`):
  - Setup: in the integ25 authority, only `libsimple_native_all.a` was replaced,
    by `cargo build --release -p simple-native-all` from this source.
    `cuda_device_query_probe.spl` was linked with `--runtime-path` to that
    directory.
  - GPU: `init=0 count=1 device=0 name=NVIDIA GB10 capability=121`, rc 0.
  - With `SIMPLE_CUDA_LIB=/nonexistent/libcuda.so.1`: `init=303 count=0
    device=-3 name=Unknown capability=-303`, rc 0, the clean
    SharedObjectInitFailed path.
  - `readelf -d`: NEEDED is libc, libstdc++, libsqlite3, libz, libzstd,
    libtinfo, libffi, libxml2, libncurses, libm and libgcc_s. There is no
    libcuda.
- **Residual.** A real bootstrap-built authority has not been produced in this
  lane. Re-run the probe with `--runtime-path` on the next Stage 2 authority.
