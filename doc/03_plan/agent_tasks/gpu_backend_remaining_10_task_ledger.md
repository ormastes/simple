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
| CompileMode | Source transport fix is committed. A trace proved explicit `--entry-closure` admitted only three direct modules because the standalone entry resolved the documentation-only `compiler.driver` facade instead of the concrete driver owner, then rejected empty MIR. Source changes now use `compiler.driver.driver` directly and avoid optional facade transport; the focused test passes, but native runtime verification is still open. An unsafe duplicate-walk attempt remained in phase 1 for more than 31 minutes and was reverted after review. No `73` executable oracle was produced. | OPEN; native rebuild required |
| Optimizer | Scalar-level repair is committed and its source guard passes, but no source-matched native driver exists after the closure-walk repair. | OPEN |
| `84` | No two-module `84` oracle binary or exact output exists after the optimizer repair. | BLOCKED by native driver rebuild |
| Vulkan | Real device is present, but the native compiler gate failed at `rt_array_data_ptr_u8`; no submit/readback receipt exists. | BLOCKED by `84` |

## Ten Tasks

| ID | Agent | Task and file | Acceptance evidence | Host | Status |
|---:|---|---|---|---|---|
| 1 | McClintock | Linux CUDA/Vulkan parity: `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl` | Real device receipts, exact pixels/checksums, zero mismatches, no CPU fallback. | Linux CUDA/Vulkan GPU | BLOCKED: CUDA lacks verified PTX; Vulkan failed the native compiler gate; rejection self-tests only |
| 2 | McClintock | Backend selector contract: `test/03_system/app/simpleos_gpu_host/backend_selector_contract_spec.spl` | Owner accepts `auto`, `cuda`, `vulkan`, `metal`; rejects unknown selectors. | Any host; source contract only | RED: owner still rejects `cuda` and `metal`; focused run exposed no conclusive harness exit |
| 3 | Confucius | Offload break-even: `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` | Native receipt records CPU/device/transfer/total/RSS medians and measured decisions. | Linux CUDA/Vulkan GPU | RED: helper check passed, but the required native measurement receipt is missing |
| 4 | Confucius | Measurement plan: `doc/03_plan/sys_test/gpu_processing_ir_offload_measurement.md` | Defines samples, schema, overhead, RSS, unavailable status, and pass/fail policy. | Linux CUDA/Vulkan GPU; macOS measurement postponed | PLAN UPDATED; UNMEASURED |
| 5 | Kierkegaard | Failure/fallback protocol: `test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl` | Validators reject forged passes and preserve unavailable, failed, mismatch, and fallback receipts. | Any host; checker boundary only | PARTIAL: 4/5 before the final edit; final edit unverified; no live injection |
| 6 | Kierkegaard | Injection matrix: `doc/03_plan/sys_test/gpu_backend_failure_injection_matrix.md` | Maps unavailable, submit, readback, mismatch, and fallback cases to hooks/evidence. | Linux for CUDA/Vulkan; prepared macOS for Metal | PLAN UPDATED; live hooks open; Metal postponed |
| 7 | Ramanujan | macOS Vulkan evidence: `test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl` | Prepared-host device-capture receipt must pass; exact identity/mismatch/delta fields remain a host TODO. | Prepared macOS Vulkan host only | TEST UPDATED; PREPARED-HOST UNRUN; Linux pending is not PASS |
| 8 | Ramanujan | macOS failure/fallback: `test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl` | Darwin harness must emit typed fail-closed Metal/Vulkan receipts. | Prepared macOS Metal/Vulkan host only | TEST UPDATED; PREPARED-HOST UNRUN; static schema only on Linux |
| 9 | Mendel | Optimizer aggregate regression: `test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl` | Source guard requires scalar level transport and direct `OptLevel` literals. | Any host for source guard; native gate on Linux/macOS | SOURCE GUARD PASS via Rust seed; source-matched native optimizer remains OPEN |
| 10 | Mendel | This ledger | Names owners, files, evidence gates, host constraints, merge owner, and reviewer. | Any | REVIEWED; GPU GOAL OPEN |

## Merge Gate

This test/plan batch may be reviewed, committed, and pushed while evidence is
open. Do not close the GPU goal until `CompileMode -> optimizer -> 84 ->
Vulkan` passes in order, task 1 produces real Linux CUDA/Vulkan receipts,
tasks 3–4 close the offload measurement, tasks 5–6 gain live injection, tasks
7–8 run on a prepared Darwin host, and the integrated result receives the
required read-only high-capability final review.
