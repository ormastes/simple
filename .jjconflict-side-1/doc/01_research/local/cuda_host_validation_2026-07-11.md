<!-- codex-research -->
# Local research: CUDA host validation

Date: 2026-07-11

## Current implementation

`scripts/check/check-cuda-generated-2d-readback.shs` already provides the core
end-to-end proof. It generates PTX through the Simple portable-compute emitter,
loads that exact PTX through the CUDA Driver API, resolves the generated fill,
copy, alpha, and scroll entries, allocates device buffers, transfers nontrivial
input host-to-device, launches and synchronizes each kernel, transfers output
device-to-host, and checks every `u32` plus position-sensitive checksums. Every
Driver API call has an operation-specific failure reason and numeric result.

The retained `doc/09_report/cuda_generated_2d_readback_2026-07-08.md` proves the
lane has passed on a CUDA host: submit and readback are true, all four operations
have zero mismatches, and aggregate expected/actual checksums match.

Compiler support is independent of device availability:

- `src/compiler/70.backend/backend/cuda_backend.spl` emits PTX and rejects
  unsupported MIR with typed backend errors.
- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`
  is the hardware-independent semantic/codegen gate.
- `scripts/check/check-portable-compute-toolchains.shs` produces and inspects
  portable CUDA artifacts without a device.
- `src/compiler/70.backend/backend/cuda/cuda_sffi.spl` exposes initialization,
  contexts, allocation, HtoD/DtoH/DtoD, module, launch, sync, and error strings;
  `cuda_launcher.spl` validates launch dimensions.
- `src/compiler_rust/runtime/src/cuda_runtime.rs` dynamically binds the Driver
  API. It is runtime support, not the authoritative Simple compiler backend.

## Availability is not correctness

The host contract needs three states:

1. `PASS`: a detected device JIT-loaded generated PTX, submitted all kernels,
   synchronized, read back output, and matched exact oracles.
2. `SKIP`: a job not designated CUDA-capable lacks the driver, device, headers,
   compiler, or assigned GPU. Portable compiler/PTX gates still must pass.
3. `FAIL`: a CUDA-capable job was requested/detected but generation, JIT,
   symbol lookup, allocation, transfer, launch, sync, readback, comparison, or
   cleanup failed. Missing CUDA on a required GPU job is configuration failure.

Thus CUDA absence on the current macOS host is not a backend failure; it only
prevents a fresh live claim.

## Gaps for the next CUDA host

- Preserve CUDA error name/string as well as the numeric result.
- Use `cuModuleLoadDataEx` and archive bounded JIT info/error logs.
- Record device UUID/name, driver version, compute capability, PTX ISA/target,
  selected device, and container/bare-metal mode.
- Add a generated `.shared`-memory kernel with a barrier and exact readback.
- Add negative live cases: malformed PTX, missing entry, invalid launch, async
  fault, and guard-region corruption.
- Preserve the primary error while reporting cleanup errors secondarily.

The host proof must execute the public Simple-produced artifact. A small C
Driver API oracle/launcher is acceptable until self-hosted native FFI proves
the same parameter-pointer ABI; it must not replace generated PTX with a
handwritten kernel.
