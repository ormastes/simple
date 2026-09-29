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

- [x] Readback gate emits an explicit tri-state `cuda_generated_2d_readback_status=pass|fail|unavailable` (SKIP is spelled `unavailable`), and the test-runner lane honours `CUDA_LIVE_REQUIRED=1` via `gpu_live_required()` — verified scripts/check/check-cuda-generated-2d-readback.shs:44 `emit_unavailable`, :280 `status=fail`, :300 `status=pass`; src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl:64 `CUDA_LIVE_REQUIRED`, :72 `gpu_live_required`
  - divergence: planned one wrapper reading `CUDA_LIVE_REQUIRED`; shipped the gate script (no `CUDA_LIVE_REQUIRED` read, `unavailable` never escalates to FAIL) plus the runner-side `gpu_live_required()` predicate in a separate module.
- [x] Gate distinguishes reasons `missing-c-compiler`, `cuda-driver-compile-failed` (missing libcuda/headers), `cuInit-failed`, `cuDeviceGetCount-failed`, `cuda-readback-run-failed` — verified scripts/check/check-cuda-generated-2d-readback.shs:843 `cuInit-failed`, :857 `cuDeviceGetCount-failed`, :1158-1172 `emit_unavailable`
  - divergence: planned separate "zero devices", "inaccessible assignment" and "required-runner provisioning" reasons; shipped zero-devices folded into `cuDeviceGetCount-failed` (:857 `device_count < 1`) and no assignment/provisioning reason.
- [ ] Use `cuModuleLoadDataEx`; archive bounded JIT logs.
- [ ] Emit CUDA numeric code plus name/string for every API failure.
- [ ] Add generated shared-memory/barrier PTX and exact CPU oracle.
- [ ] Add malformed PTX, missing symbol, launch-limit, async-fault, and guard
  negative tests.
- [ ] Add the labelled live CUDA job with `CUDA_LIVE_REQUIRED=1`. (Partial: `.github/workflows/gpu-lane-tests.yml:175` declares a `cuda-live` job on `[self-hosted, cuda-live]`, but it sets no `CUDA_LIVE_REQUIRED` and yml:17 states the runner is not provisioned — the contract lane is still open.)
- [x] Portable intensive CUDA backend contract spec lives in the unit tree and the gpu-lane workflow runs a ubuntu/macOS/Windows matrix — verified test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl:167 `rejects malformed and unsupported CUDA unary operations`, .github/workflows/gpu-lane-tests.yml:94 `runs-on: ${{ matrix.os }}`
  - divergence: the matrix job runs named A1-D2 lane specs, not the intensive contract spec explicitly; that spec is covered by the general `bin/simple test` unit run.
- [x] Report schema records device count/identity, PTX SHA-256 before/after, emitter/compiler/toolchain artifact SHA-256 and helper exit status — verified scripts/check/check-cuda-generated-2d-readback.shs:186-201 `cuda_generated_2d_readback_ptx_*_sha256`/`helper_exit_status`, doc/09_report/cuda_generated_2d_readback_2026-07-14.md:9-43 `device_identity`/`ptx_sha256_before`
  - divergence: planned JIT log + driver version in the schema; shipped no JIT log field (`grep -i jit` on the gate → 0 hits) and `cuModuleLoadData` (no `Ex` log buffers).
- [ ] Require highest-capability review of the first fresh live report.

Completion requires a fresh dedicated-host report proving the generated PTX
hash, device identity, JIT/symbol success, HtoD and DtoH, all four 2D kernels
plus shared-memory execution, synchronization, exact checksum equality, zero
element/guard mismatches, and stage-specific negative errors. Portable CI must
also prove a non-CUDA host reports live SKIP while compiler/PTX tests pass.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/cuda_host_validation_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
