# GPU Backend Remaining Ten-Task Ledger

Date: 2026-07-26

This ledger records the ten delegated lanes from this round. “Delivered” means
the test or plan exists; it does not mean the backend passed. Source markers,
cached objects, synthetic receipts, and unavailable hosts are not hardware
evidence.

## Coordination

- Merge owner: **Codex**.
- Final reviewer: **high-capability model**, read-only after integration.
- Current host: Linux x86_64. macOS lanes are postponed to prepared Darwin.
- Dependency order remains **CompileMode -> optimizer -> 84 -> Vulkan**.
- No lane may claim PASS from a full bootstrap, stub binary, CPU mirror, or
  unavailable probe.

## Ten Tasks

| ID | Agent | Task and file | Acceptance evidence | Host | Status |
|---:|---|---|---|---|---|
| 1 | McClintock | Linux CUDA/Vulkan parity: `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl` | Real device receipts, exact pixels/checksums, zero mismatches, no CPU fallback. | Linux GPU | DELIVERED; UNRUN |
| 2 | McClintock | Backend selector contract: `test/03_system/app/simpleos_gpu_host/backend_selector_contract_spec.spl` | Owner accepts `auto`, `cuda`, `vulkan`, `metal`; rejects unknown selectors. | Any | DELIVERED; expected red until owner support lands |
| 3 | Confucius | Offload break-even: `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` | Native receipt records CPU/device/transfer/total/RSS medians and measured decisions. | Linux GPU | DELIVERED; producer missing |
| 4 | Confucius | Measurement plan: `doc/03_plan/sys_test/gpu_processing_ir_offload_measurement.md` | Defines samples, schema, overhead, RSS, and pass/fail policy. | Linux GPU; macOS postponed | DELIVERED |
| 5 | Kierkegaard | Failure/fallback protocol: `test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl` | Validators reject forged passes and preserve unavailable, failed, mismatch, and fallback receipts. | Any | DELIVERED; checker-level only |
| 6 | Kierkegaard | Injection matrix: `doc/03_plan/sys_test/gpu_backend_failure_injection_matrix.md` | Maps unavailable, submit, readback, mismatch, and fallback cases to hooks/evidence. | Linux GPU; macOS postponed | DELIVERED; live hooks open |
| 7 | Ramanujan | macOS Vulkan evidence: `test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl` | Current device-capture receipt passes; exact identity/mismatch/delta fields remain a host TODO. | macOS | PARTIAL TEST; POSTPONED |
| 8 | Ramanujan | macOS failure/fallback: `test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl` | Darwin harness emits typed fail-closed Metal/Vulkan receipts. | macOS | DELIVERED; POSTPONED |
| 9 | Mendel | Optimizer aggregate regression: `test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl` | Red source guard rejects the temporary `.passes` projection implicated by the native crash. | Any | DELIVERED; EXPECTED RED until repair |
| 10 | Mendel | This ledger | Names owners, files, evidence gates, host constraints, merge owner, and reviewer. | Any | DELIVERED |

## Merge Gate

This test/plan batch may be reviewed, committed, and pushed while evidence is
open. Do not close the GPU goal until `CompileMode -> optimizer -> 84` passes,
task 1 produces real Linux CUDA/Vulkan receipts, tasks 3–4 close the offload
measurement, tasks 5–6 gain live injection, and tasks 7–8 are decided on a
prepared Darwin host.
