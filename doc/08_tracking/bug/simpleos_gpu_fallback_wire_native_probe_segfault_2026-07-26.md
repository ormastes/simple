# SimpleOS GPU Fallback Wire Request Completion Timeout

## Status

Resolved on Linux. The writable-map path, separately bounded HELLO/request
waits, and exact CUDA submit-fallback receipt are proven natively.

## Evidence

- Current-runtime host daemon build: `211 compiled, 0 failed`.
- Current-runtime probe build: `1 compiled, 18 cached, 0 failed`.
- Compiler:
  `build/gpu-goal/source-matched/simple`
  (`sha256=21fa592e16191e2b741176d1391d6e7c8e0fb2f38956537016ff62b2904ef348`).
- Source-matched daemon candidate: `1 compiled, 212 cached, 0 failed`.
- Final source-matched probe candidate: `1 compiled, 18 cached, 0 failed`
  after the initial request-wait build compiled `5` and reused `14`.
- The complete-provider runtime archive exports 20 OpenCL ABI symbols and both
  shared SIMD hit-counter symbols.
- Final threshold-`0` receipt:
  `hello_completed=true hello_status=1 hello_mask=8
  receipt_completed=true receipt_status=4 reason=16 source=2 handle=0
  identity=0 bytes=32 checksum=135272480 backend=4`.
- Interpreter execution remains inapplicable: `unknown extern function:
  rt_mmap`.
- The old runtime lacked `rt_is_interpreter_runtime`; its probes exited `139`.
- The incrementally rebuilt runtime archive exports the symbol and has SHA-256
  `2e760130f98d14e7498c29903f9bd2605d55e0e3d7d9224282c1661c107ff704`.
- Historical cycle 3 receipt before the repair:
  `hello_completed=true hello_status=1 hello_mask=8
  receipt_completed=false receipt_status=3 reason=3`.
- Cycle 3 used a 35-second daemon guard with a 60-second probe guard. The
  wrapper now derives a daemon guard 10 seconds longer than the probe guard;
  the live row was not rerun after reaching the three-cycle session cap.
- A fresh focused run confirmed the retained request loop exhausts
  `50000000` polls in about one second, before CUDA setup/fallback completion.
- An earlier shared-loop repair used the existing monotonic clock to preserve the poll
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

No compiler bootstrap was run. The essential incremental runtime-only Cargo
build used the repository's `bootstrap` optimization profile.

## Mmap Resolution

- GDB showed the first `rt_volatile_write_u64` received the correct mapped
  address and `0x53484750` value, but `rt_mmap` received tagged Simple false
  (`0x13`) for its native `readonly` argument.
- Both `file_ops` facades now declare that extern argument as `i64` and lower
  the public `bool` to explicit `0/1`.
- The existing fallback probe has a bounded `--mmap-smoke` mode. Its
  incrementally rebuilt native binary writes and reads
  `0x0000000053484750` through the writable mapping successfully.
- Incremental builds: probe `2 compiled, 17 cached`; daemon `12 compiled,
  200 cached`; both `0 failed`.
- Two intermediate uncommitted request-wait variants produced:
  `GPU_FALLBACK_WIRE status=pass hello_completed=true hello_status=1
  hello_mask=8 receipt_completed=true receipt_status=4 reason=16 source=2
  handle=0 identity=0 bytes=32 checksum=135272480 backend=4`.
- High-capability review rejected deriving a 50-second wall budget from
  `timeout_polls` and required a hard bound for frozen/backward hosted clocks.
- The third and final bounded cycle exhausted HELLO before daemon admission:
  `hello_completed=false hello_status=3 receipt_completed=false reason=7`.
  The request-wait edits were withdrawn under the three-cycle cap; the mmap ABI
  fix remains independently proven.

The broad QEMU source contract remains independently red at 6/12 due stale
assertions outside this mmap/fallback lane; it is not evidence against the
focused writable-mmap PASS above.

## Remaining Platform Evidence

Prepared-host Metal/Vulkan failure rows remain separate macOS tasks. Do not
reintroduce a synchronous compositor wait derived from poll count.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
