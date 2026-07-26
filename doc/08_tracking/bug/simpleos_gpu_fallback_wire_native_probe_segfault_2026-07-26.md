# SimpleOS GPU Fallback Wire Native Probe Segfault

## Status

Open. The end-to-end harness is implemented, but Linux native execution exits
with SIGSEGV (`139`) before publishing a wire receipt.

## Evidence

- Host daemon incremental build: `211 compiled, 0 failed`.
- Probe initial build: `18 compiled, 0 failed`; later cycles: `1 compiled,
  17 cached, 0 failed`.
- Compiler:
  `build/gpu-goal/source-matched/simple`
  (`sha256=21fa592e16191e2b741176d1391d6e7c8e0fb2f38956537016ff62b2904ef348`).
- Interpreter attempt is inapplicable: `unknown extern function: rt_mmap`.
- Native cycles 1-3 all exited `139`; cycle 3 still failed after removing the
  explicit top-level `main()` call.
- Retained logs:
  `build/simpleos_gpu_host/fallback_wire/daemon-build-source-matched.log`,
  `probe-app-build-cycle3.log`, and `probe-run-cycle3.log`.

No bootstrap was run.

## Resume

Prerequisites: Linux x86_64, CUDA, Vulkan, the retained daemon/probe binaries,
and the source-matched compiler above.

1. Debug
   `build/simpleos_gpu_host/fallback_wire/fallback_wire_probe
   --daemon=build/simpleos_gpu_host/fallback_wire/simpleos_gpu_host
   --shm=/tmp/simpleos_gpu_fallback_manual.shm` before the first application
   marker.
2. Rebuild only the changed probe with its existing `probe-app-cache`; do not
   bootstrap.
3. Run `sh scripts/check/check-simpleos-gpu-fallback-wire.shs` and retain the
   passing `GPU_FALLBACK_WIRE` receipt.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
