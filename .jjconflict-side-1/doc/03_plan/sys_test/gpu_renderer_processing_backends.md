# GPU Renderer Processing Backends System Test Plan

## Scope and ownership

This matrix traces `.spipe/gpu_renderer_processing_backends/state.md` without
absorbing unrelated dirty renderer work. Root Codex is merge owner and final
reviewer. Vulkan/web evidence is owned by the Vulkan lane; CUDA and Metal retain
their backend-specific plans and native-host blockers.

## Vulkan and production-web requirements

| Requirement | Acceptance criteria | Happy scenario | Edge scenario | Error scenario |
|---|---|---|---|---|
| REQ-001, REQ-002, REQ-011 Shared lowering, Vulkan execution, and drawing semantics | AC-1, AC-2, AC-11 | Compiler FillRect passes `spirv-val` and physical readback; production HTML/CSS reaches Vulkan device readback | One-pixel half-open rectangle preserves stride/coordinates | Out-of-bounds rectangle rejects before submission |
| REQ-006, REQ-007 Fail-closed evidence and scenario coverage | AC-6, AC-7 | Complete immutable artifact validates and native provenance matches the oracle | Changed value/coordinates invalidate semantic identity | Empty payload cannot submit or claim device origin |
| REQ-008, REQ-010 Architecture and cooperative integration | AC-8, AC-10 | Architecture names startup/hot paths, cache and resource targets | Operator guide names exact compiler/web commands | State retains merge owner, generated-manual reviewer, and unrelated-dirty-work rule |
| REQ-013 Environment and HAL readiness | AC-13 | Resolve loader/tools and validate SPIR-V before physical session admission | Classify physical device separately from software/emulator | Missing loader/tool/device/identity cannot promote readiness |
| REQ-014 CPU↔GPU communication and rendering | AC-14 | Exact upload, repeated dispatch/download, stable identity/handle, and Engine2D pixels | Reuse one retained session for two distinct outputs | Invalid handle transfer rejects without provenance |

REQ-013/014 receipts are retained under
`build/test-artifacts/02_integration/rendering/vulkan_environment_hal_communication/`;
temporary `/tmp` receipts are not accepted evidence.

Compiler-produced Vulkan evidence is retained under
`build/test-artifacts/02_integration/rendering/vulkan_compiler_fill_rect_live/`.
Production web Vulkan evidence is retained under
`build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/`.
Receipts must bind the exact command, physical evidence class, artifact/tool or
producer provenance, device identity, byte/pixel counts, checksum or artifact
SHA-256, mismatch count, and parity status.

Every mapped requirement has at least three independent happy/edge/error
scenarios. Matchers are built-in `to_equal`, `to_contain`, and
`to_be_greater_than`; no skip, TODO pass, or placeholder assertion is admitted.

## Executable evidence

- `test/01_unit/lib/common/processing/backend_contract_spec.spl`
- `test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl`
- `test/02_integration/rendering/web_vulkan_production_readback_spec.spl`
- `test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl`
- `test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl`
- CUDA: `test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl`
- Metal: `test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl`

## Complete requirement traceability

| REQ | Test files | Cases | Coverage |
|---|---|---:|---|
| REQ-001 | `backend_contract_spec.spl`, `gpu_renderer_processing_backends_spec.spl`, backend unit specs | 3+ | Full |
| REQ-002 | `vulkan_compiler_fill_rect_live_spec.spl`, `web_vulkan_production_readback_spec.spl`, Vulkan system spec | 3+ | Full on current physical Vulkan host |
| REQ-003 | `cuda_fill_u32_validation_spec.spl`, `processing_cuda_backend_spec.spl`, native CUDA contract spec | 3+ | Host-independent full; native execution blocked by TODO 650/651 |
| REQ-004 | `metal_msl_backend_spec.spl`, `processing_metal_backend_pipeline_spec.spl`, Metal system spec | 3+ | Host-independent full |
| REQ-005 | Metal unit/system specs and TODO 652 contract | 3+ | Prepared; native execution blocked by TODO 652 |
| REQ-006 | Shared contract plus Vulkan/CUDA/Metal rejection scenarios | 3+ | Full |
| REQ-007 | Backend unit, integration, and system tiers listed above | 3+ per backend | Full except blocked native rows |
| REQ-008 | Vulkan/CUDA/Metal system documentation scenarios and manuals | 3+ | Full |
| REQ-009 | Stub scan, `direct-env-runtime-guard`, generated-layout guard, and focused check commands | 4 gates | Prepared; final pure-selfhost rerun blocked |
| REQ-010 | Cooperative ownership scenario, lane plans, root manual review | 3 | Full after this root review |
| REQ-011 | Vulkan FillRect, CUDA translation, and Metal padded-stride drawing specs | 3+ per path | Full except native Metal/DirectX rows |
| REQ-012 | `cuda_drawing_translation_spec.spl`, `processing_cuda_directx_native_spec.spl`, TODO 653 contract | 3+ | Host-independent full; native execution blocked by TODO 653 |
| REQ-013 | Vulkan and CUDA HAL live specs plus Metal emulator spec | 3+ per environment | Physical Vulkan/CUDA and typed emulator coverage |
| REQ-014 | Vulkan and CUDA HAL live upload/dispatch/download scenarios | 3+ per backend | Physical Vulkan PASS; CUDA source fix prepared, rebuilt interpreter rerun required |
| REQ-015 | `metal_emulator_spec.spl` and native Metal system scenario | 4 emulator + native row | Emulator full; native Metal blocked by TODO 652 |

Mirrored manuals live under
`doc/06_spec/03_system/app/simple_2d/feature/`. No blocked native row is a
PASS: Metal and DirectX native scenarios deliberately fail after validating
their resume records, while CUDA native admission exits nonzero when its exact
source-matched probe is absent.

## Native capability matrix

| Host/capability | Required evidence | Current disposition |
|---|---|---|
| Linux physical Vulkan | Compiler-produced SPIR-V validation, physical readback, CPU parity; production web producer device provenance | Executable on current host; must PASS focused specs |
| Linux NVIDIA CUDA | Retained PTX compile/load, device readback, CPU parity | Remains blocked by the tracked pure-Simple CLI/native-build issue until resumed |
| macOS Metal | Retained MSL compile, device execution, raw parity | Remains blocked under the authoritative macOS TODO |
| Windows DirectX | HLSL compile, DirectX execution, raw parity | Remains blocked under the authoritative Windows TODO |

Unavailable native rows remain blockers, not skips or PASS. CPU mirrors are
oracles only and never satisfy native provenance.

## NFR traceability

| NFR | Evidence | Current disposition |
|---|---|---|
| NFR-001 | Backend unit determinism plus `test/05_perf/processing/metal_msl_generation_perf_spec.spl` | Prepared; 512-generation diagnostic passes, pure-selfhost rerun required |
| NFR-002 | Invalid/unsupported mutation-before-device unit scenarios and perf spec | Host-independent PASS |
| NFR-003 | Physical Vulkan compiler/web specs; CUDA/Metal/DirectX native contracts | Vulkan PASS; remaining native rows blocked |
| NFR-004 | Semantic-key mutation scenarios plus perf spec | Host-independent PASS; pure-selfhost perf rerun required |
| NFR-005 | Perf spec average generation `<10000 us` and incremental `VmHWM <8192 KiB` | Executable gate prepared; seed measurement is diagnostic only |
| NFR-006 | CUDA TODO 650/651, Metal TODO 652, DirectX TODO 653 and deliberately blocking native specs | Full blocker/resume coverage |
| NFR-007 | Vulkan/CUDA HAL retained receipts and typed Metal emulator receipt | Bounded physical/emulated classification; no presence-only promotion |

## Environment, HAL, and CPU/GPU communication matrix

| Backend | Environment owner | Transfer/dispatch/readback evidence | Class | Status |
|---|---|---|---|---|
| Vulkan | `VulkanSession` + Engine2D | 64-byte upload, two dispatches, exact download, stable handle/identity, Engine2D pixels, invalid handle rejection | `physical-device` | PASS 3/3 on RTX A6000 |
| CUDA | `CudaSession` + dynamic CUDA interpreter extern | CPU `[1,2,10,100]`, PTX `+7`, two downloads `[8,9,17,107]`, stable context/module/device, invalid transfer normalization | `physical-device` | Physical happy/reuse passed; exact-error rerun waits for rebuilt interpreter |
| Metal | shared artifact contract + `metal_emulator` | bindings 0/1/2, upload, FillRect dispatch, padding/readback parity, repeated dispatch, invalid source/entry/binding/transfer rejection | `emulator` | PASS 4/4; not native proof |
| Metal native | exact `processing_ir_execute_metal_artifact` owner | same semantic scenario with raw Metal readback | `physical-device` | BLOCKED under TODO 652 |

The aggregate admission gate is
`test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl`
with manual
`doc/06_spec/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.md`.
It requires the retained physical/emulator receipts above and deliberately
fails until native Metal and DirectX physical rows close. A green subset is not
reported as “100% external environment qualification.”

## Focused commands

```text
bin/simple test test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl --mode=interpreter --no-session-daemon
bin/simple test test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl --mode=interpreter --no-session-daemon
bin/simple test test/02_integration/rendering/web_vulkan_production_readback_spec.spl --mode=interpreter --no-session-daemon
```

Run each unchanged green command once. Stop after three fix/verify cycles.

## NFR-008 branch coverage measurement

The focused contract suite exercises explicit success, boundary, and rejection
branches using the canonical steps `Exercise success branches`, `Exercise
boundary branches`, `Exercise rejection branches`, and `Measure branch
coverage`. The documented `--coverage` command passed 7/7 scenarios but emitted
no per-file branch data. Therefore numerator, denominator, and percentage remain
`unavailable`, not inferred from scenario count. The machine-readable blocked
receipts are retained under
`build/test-artifacts/coverage/gpu_renderer_processing_backends/` for the
shared/Vulkan, CUDA, and Metal scopes. All link the existing coverage-tooling
bug and explicitly reject statement percentages as branch coverage. The >=80%
gate remains blocking until the runner emits a compiler-owned source decision
inventory and true/false outcome numerator/denominator.
