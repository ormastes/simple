# GPU Backend Remaining Ten-Task Ledger

Date: 2026-07-26

This ledger records the ten delegated lanes from this round. “Delivered” means
the test or plan exists; it does not mean the backend passed. Source markers,
cached objects, synthetic receipts, and unavailable hosts are not hardware
evidence.

## Coordination

- Merge owner: **Codex**.
- Final reviewer: **high-capability model**, read-only after integration. This
  coordination review is pre-integration and does not satisfy that final gate.
- Current host: Linux x86_64 with CUDA and Vulkan devices. Metal and every
  macOS runtime claim are postponed to a prepared Darwin host.
- Dependency order remains **CompileMode -> optimizer -> 84 -> Vulkan**.
- No lane may claim PASS from a full bootstrap, stub binary, CPU mirror, or
  unavailable probe.

## Ordered Dependency Gate

| Gate | Current evidence | State |
|---|---|---|
| CompileMode | Source transport, `pub mod`, and MIR isolation fixes are committed; focused coverage passes. Three distinct bridge shapes proved the old compiler crashes on bootstrap-reachable `CompileOptions` aggregate construction: the general dispatcher, mutate-after-default helper, and direct full literal all fail during HIR. Canonical source was restored after every attempt; no bridge or `73` executable was produced. | OPEN; old-generation bootstrap aggregate HIR crash |
| Optimizer | Scalar-level repair is committed and its source guard passes, but no source-matched native driver exists after the closure-owner repair. | OPEN |
| `84` | No two-module `84` oracle binary or exact output exists after the optimizer repair. | BLOCKED by source-matched CLI generation |
| Vulkan | Real device is present. The SFFI owner routes interpreter arrays through typed upload/SPIR-V/push/readback externs and preserves raw core-C native ABI; the unsafe generic TLS shim remains rejected. Interpreter and native Rust runtime device tests pass nonzero-offset exact readback plus OOB rejection. | INTERPRETER + NATIVE RUNTIME DEVICE PASS; source-matched Simple native evidence pending |

## Ten Tasks

| ID | Agent | Task and file | Acceptance evidence | Host | Status |
|---:|---|---|---|---|---|
| 1 | McClintock | Linux CUDA/Vulkan parity: `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl` | Real device receipts, exact pixels/checksums, zero mismatches, no CPU fallback. | Linux CUDA/Vulkan GPU | PARTIAL: CUDA current-emitter -> verified `nvcc` PTX -> device readback passes with zero mismatches; Vulkan interpreter and native runtime byte round-trips pass; source-matched Simple native Vulkan processing receipt remains open |
| 2 | McClintock | Backend selector contract: `test/03_system/app/simpleos_gpu_host/backend_selector_contract_spec.spl` | Owner accepts `auto`, `cuda`, `vulkan`, `metal`; rejects unknown selectors; explicit selectors narrow to one backend before probing. | Any host; source contract only | GREEN: focused contract passes 3/3 |
| 3 | Confucius | Offload break-even: `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` | Native receipt records CPU/device/transfer/total/RSS medians and measured decisions. | Linux CUDA GPU | GREEN: current-emitter PTX provenance and exact device readback pass; CPU wins at 64/65,536 elements and CUDA wins at 1,048,576/8,388,608; focused consumer passes 2/2 |
| 4 | Confucius | Measurement plan: `doc/03_plan/sys_test/gpu_processing_ir_offload_measurement.md` | Defines samples, schema, overhead, RSS, unavailable status, and pass/fail policy. | Linux CUDA GPU; Vulkan/macOS measurement postponed | MEASURED: break-even 1,048,576 elements; median communication overhead 1,832 us at transition |
| 5 | Kierkegaard | Failure/fallback protocol: `test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl` | Validators reject forged passes and preserve unavailable, failed, mismatch, and fallback receipts. | Any host; checker boundary only | GREEN: checker contract passes 5/5; live injection remains task 6 |
| 6 | Kierkegaard | Injection matrix: `doc/03_plan/sys_test/gpu_backend_failure_injection_matrix.md` | Maps unavailable, submit, readback, mismatch, and fallback cases to hooks/evidence. | Linux for CUDA/Vulkan; prepared macOS for Metal | PARTIAL: disabled-by-default CUDA init/submit/readback/mismatch hooks pass live; Vulkan hooks are implemented but current runtime lacks `rt_vulkan_dependency_quarantine_lock`; Metal postponed |
| 7 | Ramanujan | macOS Vulkan evidence: `test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl` | Prepared-host device-capture receipt must pass; exact identity/mismatch/delta fields remain a host TODO. | Prepared macOS Vulkan host only | TEST UPDATED; PREPARED-HOST UNRUN; Linux pending is not PASS |
| 8 | Ramanujan | macOS failure/fallback: `test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl` | Darwin harness must emit typed fail-closed Metal/Vulkan receipts. | Prepared macOS Metal/Vulkan host only | TEST UPDATED; PREPARED-HOST UNRUN; static schema only on Linux |
| 9 | Mendel | Optimizer aggregate regression: `test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl` | Source guard requires scalar level transport and direct `OptLevel` literals. | Any host for source guard; native gate on Linux/macOS | SOURCE GUARD PASS via Rust seed; source-matched native optimizer remains OPEN |
| 10 | Mendel | This ledger | Names owners, files, evidence gates, host constraints, merge owner, and reviewer. | Any | REVIEWED; GPU GOAL OPEN |

## Vulkan Interpreter Byte Transport TODO

Do not add a single copied TLS buffer behind `rt_array_data_ptr_u8`. The
dual-ABI SFFI replacement preserves these contracts by avoiding raw interpreter
pointers:

1. Native writes must update the Simple `[u8]` returned by Vulkan readback.
2. Multiple byte pointers passed to one extern call must remain valid together.
3. Empty arrays must match the native runtime's null-pointer contract.

The array-valued Vulkan readback extern is selected by the immutable runtime
kind intrinsic; native runs retain the raw core-C ABI. Interpreter and native
runtime upload/readback checks pass. Keep this task open until the same
empty/OOB and device-readback checks pass from a source-matched Simple native
executable without a bootstrap-only claim.

Retained interpreter evidence:
`build/gpu-goal/dual-abi/vulkan-live-readback-cycle3.log`.

Retained CUDA source/toolchain/device evidence:
`build/native_processing_ir_cuda_vulkan_readback_parity/cuda/evidence.env`.

## Merge Gate

This test/plan batch may be reviewed, committed, and pushed while evidence is
open. Do not close the GPU goal until `CompileMode -> optimizer -> 84 ->
Vulkan` passes in order, task 1 produces real Linux CUDA/Vulkan receipts,
tasks 3–4 are closed for Linux CUDA, tasks 5–6 gain live injection, tasks
7–8 run on a prepared Darwin host, and the integrated result receives the
required read-only high-capability final review.
