# Natively linked CUDA program: rt_cuda_init never opens libcuda, so init returns cuda-init-failed

- **Date:** 2026-11-22
- **Status:** open
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
