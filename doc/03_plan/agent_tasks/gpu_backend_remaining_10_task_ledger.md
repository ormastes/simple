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
| Vulkan | Real device is present. The SFFI owner routes interpreter arrays through typed upload/SPIR-V/push/readback externs and preserves raw core-C native ABI; the unsafe generic TLS shim remains rejected. A current-source runtime and native probe pass 64 exact iterated values with RTX A6000 identity `666008366` plus all five isolated fault phases. | CURRENT-SOURCE SIMPLE NATIVE DEVICE + FAULT PASS |

## Ten Tasks

| ID | Agent | Task and file | Acceptance evidence | Host | Status |
|---:|---|---|---|---|---|
| 1 | McClintock | Linux CUDA/Vulkan parity: `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl` | Real device receipts, exact pixels/checksums, zero mismatches, no CPU fallback. | Linux CUDA/Vulkan GPU | GREEN: current-source CUDA daemon evidence passes eight exact 1,048,576-element device receipts with stable provenance and no fallback. Vulkan storage readback now inserts the required compute-shader-write/transfer-write to transfer-read barrier; its focused mask unit passes 1/1 and the strict relinked probe passes 64 exact values with RTX A6000 identity `666008366` plus all five fault phases and same-process recovery. Direct indexed-array transport remains separate compiler work. |
| 2 | McClintock | Backend selector contract: `test/03_system/app/simpleos_gpu_host/backend_selector_contract_spec.spl` | Owner accepts `auto`, `cuda`, `vulkan`, `metal`; rejects unknown selectors; explicit selectors narrow to one backend before probing. | Any host; source contract only | GREEN: focused contract passes 3/3 |
| 3 | Confucius | Offload break-even: `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` | Native receipt records CPU/device/transfer/total/RSS medians and measured decisions. | Linux CUDA GPU | GREEN baseline: generated-CUDA round trip selects CPU at 64/65,536 and GPU at 1,048,576/8,388,608. The direct ProcessingIR candidate completes exactly at 1,048,576 with device provenance and no fallback. The prior daemon-wire gate passed 3 warmups plus 5 measured exact requests with stable provenance; medians were 155110 us device, 312012 us round trip, 156902 us non-device overhead, and 82097 us CPU. Default requests avoid the duplicate CPU result and fuse exact-length FillU32 validation with wire copy; runtime unit 1/1, symbol-table tests, policy contract 10/10, and strict no-stub pure-Simple native ABI smoke pass. `device-warm` opts into `--processing-verify-cpu`, while `device-warm-production` requires explicit verifier-disabled startup and rejects any CPU comparison record. The retained old daemon's 116663/236498/119835 us repeat is historical under the prior checker. Fresh source-matched medians remain required; stable-input, non-admitted Stage3 candidate `c2a638a5...` clears the parser failure but loses `common.ui.draw_ir` imported struct types during entry-closure lowering. |
| 4 | Confucius | Measurement plan: `doc/03_plan/sys_test/gpu_processing_ir_offload_measurement.md` | Defines samples, schema, overhead, RSS, unavailable status, and pass/fail policy. | Linux CUDA GPU; Vulkan/macOS measurement postponed | MEASURED: break-even 1,048,576 elements; median communication overhead 1,832 us at transition |
| 5 | Kierkegaard | Failure/fallback protocol: `test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl` | Validators reject forged passes and preserve unavailable, failed, mismatch, and fallback receipts. | Any host; checker boundary only | GREEN: checker contract passes 5/5; typed executor-to-wire reason mapping passes 6/6 across CUDA/Vulkan/Metal, with native driver prose contained behind stable tokens; pre-device validation passes CUDA 1/1, Vulkan 2/2, and Metal 2/2; shared cleanup/quarantine ownership passes 8/8. Native Linux CUDA submit injection returns exact reason `16`; native Linux Vulkan passes unavailable/init/submit/readback/mismatch isolation. Prepared-host Metal remains task 6. |
| 6 | Kierkegaard | Injection matrix: `doc/03_plan/sys_test/gpu_backend_failure_injection_matrix.md` | Maps unavailable, submit, readback, mismatch, and fallback cases to hooks/evidence. | Linux for CUDA/Vulkan; prepared macOS for Metal | PARTIAL: writable mmap ABI smoke passes. Current-source Vulkan default plus all five isolated fault phases pass after the storage readback memory-dependency repair, and same-process submit failure recovers to 64 exact values with unchanged identity. The checker requires one fully anchored receipt per process and rejects contradictory extra receipts. Deterministic Linux CUDA submit fallback completes with exact reason `16`; same-process CUDA baseline/readback-failure/recovery now passes exact checksum `1082179840`, zero failure provenance, and unchanged identity `1002905313239842438`. Prepared-macOS Metal phases remain open. |
| 7 | Ramanujan | macOS Vulkan evidence: `test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl` | Prepared-host device-capture receipt must pass; exact ProcessingIR checksum, positive identity, zero mismatches, device readback, and no CPU fallback are mandatory. | Prepared macOS Vulkan host only | LINUX CONTRACT PASS 5/5: canonical harness/checker ownership is enforced and the fixed 64-value checksum is pinned to `1082179840`. PREPARED-HOST UNRUN; Linux pending is not runtime PASS. |
| 8 | Ramanujan | macOS failure/fallback: `test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl` | Darwin harness must emit typed fail-closed Metal/Vulkan receipts. | Prepared macOS Metal/Vulkan host only | LINUX CONTRACT PASS: backend-create failures include canonical backend/stage/exit fields; Metal children are bounded to 30 s/4 MiB and only an actual runtime timeout receives the timeout marker. The Metal executor now reports actual runtime absence as `metal-unavailable` before initialization, while init/zero-device failures remain `metal-init-failed`. The prepared no-fault probe requires eight exact FillU32 values and checksum `135272480`; the shared fault source contract passes 10/10. Prepared-host receipts remain unrun. |
| 9 | Mendel | Optimizer aggregate regression: `test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl` | Source guard requires scalar level transport and direct `OptLevel` literals. | Any host for source guard; native gate on Linux/macOS | SOURCE GUARD PASS via Rust seed. The `73` promotion spec requires hash-bound non-seed producer/runtime artifacts, exact Stage4/no-stub profile, stale-output deletion, bounded children, and non-fatal hint suppression; its Linux source contract passes 1/1, while the live example is registered only when all prepared inputs exist. A current incremental producer cleared the stale extern blocker but was terminated after no retained post-load log/cache progress; 13,683 non-fatal common-mistake hints were identified in that output path. |
| 10 | Mendel | This ledger | Names owners, files, evidence gates, host constraints, merge owner, and reviewer. | Any | REVIEWED; GPU GOAL OPEN |

## Vulkan Interpreter Byte Transport Evidence

Do not add a single copied TLS buffer behind `rt_array_data_ptr_u8`. The
dual-ABI SFFI replacement preserves these contracts by avoiding raw interpreter
pointers:

1. Native writes must update the Simple `[u8]` returned by Vulkan readback.
2. Multiple byte pointers passed to one extern call must remain valid together.
3. Empty arrays must match the native runtime's null-pointer contract.

The array-valued Vulkan readback extern is selected by the immutable runtime
kind intrinsic; native runs retain the raw core-C ABI. Interpreter and native
runtime upload/readback checks pass. The retained Simple native probe candidate
passes exact device readback and all five isolated fault phases. The direct
CUDA ProcessingIR candidate and aggregate gate now pass the same iterator-based
device receipt contract; direct indexing remains open compiler work.

Retained interpreter evidence:
`build/gpu-goal/dual-abi/vulkan-live-readback-cycle3.log`.

Retained CUDA source/toolchain/device evidence:
`build/native_processing_ir_cuda_vulkan_readback_parity/cuda/evidence.env`.

## Merge Gate

This test/plan batch may be reviewed, committed, and pushed while evidence is
open. Do not close the GPU goal until `CompileMode -> optimizer -> 84 ->
Vulkan` passes in order, tasks 3–4 are closed for Linux CUDA, tasks 5–6 gain live injection, tasks
7–8 run on a prepared Darwin host, and the integrated result receives the
required read-only high-capability final review.
