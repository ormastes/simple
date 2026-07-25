# CUDA-enabled host validation plan and TODO

Date: 2026-07-11

## Contract

The runner accepts `CUDA_LIVE_REQUIRED=0|1` (default `0`) and emits one state:

- `PASS`: live proof completes with zero mismatches.
- `SKIP`: live CUDA is optional and the driver/device/toolchain/assigned GPU is
  absent. Exit 0; portable PTX/backend gates remain mandatory.
- `FAIL`: compiler/backend failure; or detection, JIT, symbol, memory, launch,
  sync, comparison, or cleanup failure after CUDA is required/detected.

Never convert invalid PTX, JIT incompatibility, a missing symbol, launch error,
sync error, or readback mismatch to SKIP.

## Exact positive sequence

1. Generate PTX once from the canonical Simple emitter; record SHA-256,
   `.version`, `.target`, `.address_size`, and entry names.
2. Load `libcuda`; call `cuInit(0)` and `cuDeviceGetCount`; select configured
   device 0 by default. Record driver, device name/UUID, and capability.
3. Retain/set one context. JIT the exact bytes with `cuModuleLoadDataEx` and
   bounded info/error buffers. Resolve every required entry.
4. Allocate independent input/output buffers with guard regions. Upload
   position-sensitive nonuniform host vectors; check every result.
5. Launch fill, copy, alpha, and scroll over multiple blocks and a non-divisible
   count. Check the immediate launch result, `cuCtxSynchronize`, and DtoH.
6. Compare every output and guard element and a 64-bit position-sensitive
   checksum against CPU oracles. Tolerance is zero.
7. Launch a generated shared-memory kernel: each thread loads a distinct input
   into block-local `.shared`, executes a barrier, reads a neighbor, and stores
   a deterministic result. Use at least two blocks and explicit dynamic bytes
   when applicable; synchronize/read back and compare every element.
8. Free buffers, unload the module, and release the context. Preserve the first
   operational error and append cleanup errors as secondary diagnostics.

## Required negative cases

| Condition | Result |
|---|---|
| malformed PTX | FAIL at JIT with code, name/string, and JIT log |
| rejected target/version | FAIL as PTX/JIT incompatibility, never SKIP |
| nonexistent entry | FAIL at symbol resolution |
| zero/oversized launch | FAIL at validation/launch with operation name |
| allocation/HtoD failure | FAIL before submit; no false readback claim |
| asynchronous fault | retain launch result; FAIL at synchronization |
| DtoH failure | FAIL with `readback_available=false` |
| output/sentinel mismatch | FAIL with checksums and first mismatch index |
| no device on optional host | SKIP; portable gates still required |
| no device on required GPU job | FAIL as runner provisioning error |

## CI

- Use a dedicated runner label such as `cuda-live`; do not infer all Linux
  runners have CUDA.
- Driver API enumeration is authoritative; record `nvidia-smi -L` only as
  diagnostics.
- Containers explicitly request a GPU and `compute,utility` capabilities.
- Set `CUDA_LIVE_REQUIRED=1` only on the dedicated lane.
- Hash and execute the artifact generated in the same job. Archive PTX, build
  output, JIT logs, device metadata, evidence, and expected/actual buffers.

## TODO

- [ ] Implement explicit PASS/SKIP/FAIL in the CUDA readback wrapper.
- [ ] Distinguish missing library, init failure, zero devices, inaccessible
  assignment, and required-runner provisioning failure.
- [ ] Use `cuModuleLoadDataEx`; archive bounded JIT logs.
- [ ] Emit CUDA numeric code plus name/string for every API failure.
- [ ] Add generated shared-memory/barrier PTX and exact CPU oracle.
- [ ] Add malformed PTX, missing symbol, launch-limit, async-fault, and guard
  negative tests.
- [ ] Add the labelled live CUDA job with `CUDA_LIVE_REQUIRED=1`.
- [ ] Keep portable intensive CUDA tests on every platform.
- [ ] Record device/JIT/artifact provenance in the report schema.
- [ ] Require highest-capability review of the first fresh live report.

Completion requires a fresh dedicated-host report proving the generated PTX
hash, device identity, JIT/symbol success, HtoD and DtoH, all four 2D kernels
plus shared-memory execution, synchronization, exact checksum equality, zero
element/guard mismatches, and stage-specific negative errors. Portable CI must
also prove a non-CUDA host reports live SKIP while compiler/PTX tests pass.
