# SimpleOS GPU Fallback Wire Request Completion Timeout

## Status

Open. The retained current-runtime probe reaches HELLO with CUDA mask `8`, but
the following processing request times out before fallback completion.
Recompiling the shared ivshmem bridge with the retained source-matched compiler
reintroduces the native `file_mmap`/MMIO ABI SIGSEGV before HELLO completes.

## Evidence

- Current-runtime host daemon build: `211 compiled, 0 failed`.
- Current-runtime probe build: `1 compiled, 18 cached, 0 failed`.
- Compiler:
  `build/gpu-goal/source-matched/simple`
  (`sha256=21fa592e16191e2b741176d1391d6e7c8e0fb2f38956537016ff62b2904ef348`).
- Interpreter execution remains inapplicable: `unknown extern function:
  rt_mmap`.
- The old runtime lacked `rt_is_interpreter_runtime`; its probes exited `139`.
- The incrementally rebuilt runtime archive exports the symbol and has SHA-256
  `2e760130f98d14e7498c29903f9bd2605d55e0e3d7d9224282c1661c107ff704`.
- Current cycle 3 receipt:
  `hello_completed=true hello_status=1 hello_mask=8
  receipt_completed=false receipt_status=3 reason=3`.
- Cycle 3 used a 35-second daemon guard with a 60-second probe guard. The
  wrapper now derives a daemon guard 10 seconds longer than the probe guard;
  the live row was not rerun after reaching the three-cycle session cap.
- A fresh focused run confirmed the retained request loop exhausts
  `50000000` polls in about one second, before CUDA setup/fallback completion.
- A shared-loop repair used the existing monotonic clock to preserve the poll
  floor while enforcing the same numeric microsecond budget. It compiled
  incrementally, but both the compiler runtime overlay and the current
  Vulkan/CUDA runtime link produced a probe that SIGSEGVs in
  `rt_volatile_write_u64` called by `host_gpu_ivshmem_negotiate`.
- The debugger confirms the repaired wait loop is never reached. The source
  and test edits were withdrawn rather than pushing unverified production
  code. Three focused verify/fix cycles are exhausted.
- Retained logs:
  `build/simpleos_gpu_host/fallback_wire/daemon-build-current-runtime.log`,
  `probe-build-shell-owned.log`, `daemon-live.log`, and
  `wrapper-current-runtime-cycle3.log`.

No compiler bootstrap was run. One essential incremental runtime-only Cargo
build used the repository's `bootstrap` optimization profile.

## Resume

Prerequisites: Linux x86_64, CUDA, Vulkan, the retained current-runtime
daemon/probe binaries, and the source-matched compiler above.

1. Repair or replace the source-matched compiler so recompiling
   `host_gpu_ivshmem.spl` preserves the working `file_mmap`/MMIO ABI.
2. Reapply a clock-bounded wait in shared `_host_gpu_publish_payload`; keep
   poll count as the invalid-clock fallback.
3. Incrementally rebuild only the probe, then run
   `sh scripts/check/check-simpleos-gpu-fallback-wire.shs` once and retain the
   passing `GPU_FALLBACK_WIRE` receipt.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
