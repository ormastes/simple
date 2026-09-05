# The 27 env-gated specs: 12 are tautology shells, 7 hide real defects

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Filed:** 2026-08-09 (stream P15)
**Follows:** `env_gated_spec_switches_are_inert_under_test_daemon_2026-08-09.md` (P14, `c3307d1404d`)

P14 landed the runner bypass and left one question open: *do the 27 specs'
hardware branches actually pass once they really run?* P15 ran all 27 with their
gate set, via P14's `env_gate_bypass` (every run printed
`test-env-gate: <VAR> set; bypassing test daemon`). All 27 produced a verdict
line. **Zero hangs.**

The answer is worse than "some fail".

## Headline: for 12 of the 27, there is no hardware branch to run

Their `it` bodies contain *only* the gate assertion, written to expect the
**closed** value:

```
# test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl — ALL 11 it-bodies are this line
it "AC-2: is_available detects CUDA runtime":
    expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

The file never references `CudaFfi`, yet its header claims
`@cover src/lib/gc_async_mut/gpu/engine2d/ffi_cuda.spl 80%`. These specs are
green only because the gate is shut; opening it makes them fail 100%
deterministically with `expected ready to equal blocked:<GATE>`. They assert the
absence of testing. Closing the gate was never hiding a hardware failure — it was
hiding that no test exists.

Census (`it` count | gate-tautology count):

| spec | its | tautologies |
|---|---|---|
| gpu/engine2d/backend_qualcomm | 12 | 12 |
| gpu/engine2d/device_detect | 14 | 14 |
| gpu/engine2d/ffi_cuda | 11 | 11 |
| gpu/engine2d/ffi_intel | 11 | 11 |
| gpu/engine2d/ffi_vulkan | 12 | 12 |
| gpu/engine2d/ffi_rocm | 13 | 10 |
| gpu/engine2d/engine_platform | 20 | 10 |
| feature/usage/vulkan | 9 | 9 |
| feature/usage/vhdl | 8 | 8 |
| feature/usage/vhdl_golden | 2 | 2 |
| feature/usage/tensor_interface | 1 | 1 |
| app/serial_mcp/serial_mcp | 12 | 4 |

Note none of these is FAIL-ENV. `ffi_cuda` and `vulkan` fail on a host where
CUDA and Vulkan genuinely work (P13/P6). Hardware presence is irrelevant to a
tautology.

## Full table

| spec | gate | verbatim verdict (`SPEC FILE VERDICT: <path> ...`) | class | diagnosis |
|---|---|---|---|---|
| app/serial_mcp/serial_mcp | HW | `declared>=12 executed=12 passed=6 failed=6 dropped=0` | FAIL-REAL | 4 tautology its + 2 more assert closed gate |
| gpu/engine2d/backend_qualcomm | GPU | `declared>=12 executed=12 passed=0 failed=12 dropped=0` | FAIL-REAL | tautology shell, no Qualcomm code touched |
| gpu/engine2d/device_detect | GPU | `declared>=14 executed=14 passed=0 failed=14 dropped=0` | FAIL-REAL | tautology shell |
| gpu/engine2d/engine_platform | GPU | `declared>=20 executed=20 passed=9 failed=11 dropped=0` | FAIL-REAL | 10 tautologies + 1 `expected false to equal true` |
| gpu/engine2d/ffi_cuda | GPU | `declared>=11 executed=11 passed=0 failed=11 dropped=0` | FAIL-REAL | tautology shell; claims `@cover 80%` |
| gpu/engine2d/ffi_intel | GPU | `declared>=11 executed=11 passed=0 failed=11 dropped=0` | FAIL-REAL | tautology shell |
| gpu/engine2d/ffi_rocm | GPU | `declared>=13 executed=13 passed=3 failed=10 dropped=0` | FAIL-REAL | tautology shell |
| gpu/engine2d/ffi_vulkan | GPU | `declared>=12 executed=12 passed=0 failed=12 dropped=0` | FAIL-REAL | tautology shell; Vulkan works on this host |
| gc_async_mut/processing/fault_injection | GPU | `declared>=2 executed=2 passed=2 failed=0 dropped=0` | PASS | real body, green |
| simpleos_gpu_host/gpu_backend_failure_injection | GPU | `declared>=5 executed=5 passed=5 failed=0 dropped=0` | PASS | real body, green |
| simpleos_gpu_host/macos_metal_processing_ir_failure_injection | GPU | `declared>=3 executed=2 passed=1 failed=0 dropped=1` | PASS | correctly *drops* the Metal case; the one spec with a proper hardware skip |
| simpleos_gpu_host/processing_ir_fault_source_contract | GPU | `declared>=10 executed=10 passed=10 failed=0 dropped=0` | PASS | real body, green |
| simpleos_gpu_host/processing_vulkan_fault_native_contract | GPU | `declared>=3 executed=3 passed=3 failed=0 dropped=0` | PASS | real body, green |
| feature/usage/tensor_interface | GPU | `declared>=1 executed=1 passed=0 failed=1 dropped=0` | FAIL-REAL | tautology shell |
| feature/usage/vulkan | GPU | `declared>=9 executed=9 passed=0 failed=9 dropped=0` | FAIL-REAL | tautology shell |
| feature/usage/cuda | CUDA | `declared>=5 executed=5 passed=4 failed=1 dropped=0` | FAIL-REAL | `expected -3 to be greater than 0` — CUDA call returns error code where a positive count is required |
| feature/usage/gpu_ptx_gen | CUDA | `declared>=81 executed=81 passed=69 failed=12 dropped=0` | FAIL-REAL | PTX atomics emitted as `.u64`/`.b64`, spec requires `.s64` (`atom.global.add`, `atom.global.cas`) |
| io_audio/simple_audio_cuda_q15_env | CUDA | `declared>=1 executed=1 passed=0 failed=1 dropped=0` | FAIL-REAL | `expected 0 to equal -2048` — Q15 CUDA path yields 0 |
| feature/usage/llvm_backend | LLVM | `declared>=32 executed=32 passed=24 failed=8 dropped=0` | FAIL-REAL | 8x `expected subject to be truthy, got 0.0` |
| feature/usage/llvm_backend_aarch64 | LLVM | `declared>=10 executed=10 passed=9 failed=1 dropped=0` | FAIL-REAL | `semantic: class LlvmIRBuilder has no field named instructions` (datalayout test) |
| feature/usage/llvm_backend_arm32 | LLVM | `declared>=10 executed=10 passed=10 failed=0 dropped=0` | PASS | |
| feature/usage/llvm_backend_i686 | LLVM | `declared>=10 executed=10 passed=9 failed=1 dropped=0` | FAIL-REAL | same `LlvmIRBuilder.instructions` API drift |
| feature/usage/llvm_backend_riscv32 | LLVM | `declared>=9 executed=9 passed=9 failed=0 dropped=0` | PASS | |
| feature/usage/llvm_backend_riscv64 | LLVM | `declared>=9 executed=9 passed=9 failed=0 dropped=0` | PASS | |
| feature/usage/vhdl | VHDL | `declared>=8 executed=8 passed=0 failed=8 dropped=0` | FAIL-REAL | tautology shell |
| feature/usage/vhdl_golden | VHDL | `declared>=2 executed=2 passed=0 failed=2 dropped=0` | FAIL-REAL | tautology shell |
| feature/usage/wasm_compile | WASM | `declared>=36 executed=36 passed=34 failed=2 dropped=0` | FAIL-REAL | `expected const x = 1; to equal true`; `expected nil to equal false` |

## Totals

| class | count |
|---|---|
| PASS | 8 |
| FAIL-REAL | 19 (12 tautology shells + 7 genuine defects) |
| FAIL-ENV | 0 |
| HANG | 0 |

**FAIL-ENV is zero, and that is the point.** P14 predicted Metal and Qualcomm as
the likely casualties. Metal is the *one* spec that behaves correctly
(`dropped=1`). Qualcomm fails not for lack of a Snapdragon but because its spec
tests nothing. No spec failed for want of hardware.

## The 7 genuine defects the closed gates were hiding

1. `feature/usage/cuda` — CUDA call returns `-3` where a positive count is required.
2. `feature/usage/gpu_ptx_gen` — PTX atomic width/sign mismatch: emits
   `atom.global.add.u64` / `atom.global.cas.b64`, spec requires `.s64`. 12 cases.
3. `io_audio/simple_audio_cuda_q15_env` — Q15 CUDA result 0, expected -2048.
4. `feature/usage/llvm_backend` — 8 truthiness assertions get `0.0`.
5. `feature/usage/llvm_backend_aarch64` — `LlvmIRBuilder` has no field `instructions`.
6. `feature/usage/llvm_backend_i686` — same API drift.
7. `feature/usage/wasm_compile` — 2 assertions get raw source text / `nil`
   where a bool is expected.

## Recommended disposition (NOT done here — this stream is an audit)

- The 12 tautology shells must not be "fixed" by flipping the expected value to
  `ready`. That converts a vacuous spec into a differently vacuous spec. They
  need real bodies, or deletion plus an honest coverage number — their `@cover`
  claims are currently false.
- The 7 genuine defects each want their own bug and fix stream.
- Do not add hardware skip guards wholesale. Guards are how these 27 became
  invisible in the first place. `macos_metal_...` shows the correct shape: run
  the spec, drop the one case the host cannot serve.

## Reproduce

```bash
SIMPLE_MODULE_LIMIT=4000 SIMPLE_TIMEOUT_SECONDS=3600 SIMPLE_GPU_TEST=1 \
  bin/simple test test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl
```
