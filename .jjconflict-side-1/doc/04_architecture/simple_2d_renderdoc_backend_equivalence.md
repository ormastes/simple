<!-- codex-architecture -->
# Simple 2D RenderDoc Backend Equivalence Architecture

## Status

Accepted for selected Feature C + NFR B. The feature is an opt-in evidence capsule: pure common record/diff/equivalence types, backend-owned snapshots, Engine2D facade capture, and platform evidence adapters. Normal rendering does not perform serialization, hashing, replay, or subprocess work.

## Decisions

- **D-1:** `common.renderdoc` owns one versioned schema and pure algorithms; it imports no backend, file, environment, process, or runtime surface.
- **D-2:** exact record equality preserves every provenance difference; cross-backend equivalence uses an explicit semantic projection and never normalizes backend/API/adapter/driver/handle/completion/pipeline/resource/readback facts.
- **D-3:** `RenderBackend` exposes an opt-in typed snapshot. Vulkan, DirectX, Metal, and software implement real snapshots; other backends return typed `unsupported-backend`, never fabricated records.
- **D-4:** Engine2D records requested vs actual backend and translation explicitly. Linux compatibility lanes are `directx-request→vulkan` and `metal-request→vulkan`; they do not claim DXVK, native D3D, or native Metal.
- **D-5:** RenderDoc CLI replay-open plus artifact/action markers corroborate capture validity. Four-byte magic is only a precheck; no new Python/Bash record implementation is introduced.
- **D-6:** one aggregate owns focused/intensive/qualification profiles. Linux PASS requires physical/software Vulkan and both explicit Vulkan compatibility lanes; full qualification remains externally incomplete until native Windows/macOS rows pass.
- **D-7:** MDSOC is applied as a virtual evidence capsule, not a feature transform: recording is explicitly enabled and does not weave overhead into ordinary application frames.
- **D-8:** SimpleOS uses a bounded noalloc-compatible `BackendRenderReceipt` event stream emitted from the guest and expanded by the host into the common record. QMP or board capture corroborates pixels; host RenderDoc is optional corroboration and never a guest dependency.

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.architecture -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR
WebFixtures -> ProductionWebFacade
PrimitiveFixtures -> Engine2DFacade
ProductionWebFacade -> Engine2DFacade
Engine2DFacade -> BackendSnapshot
BackendSnapshot -> VulkanOwner
BackendSnapshot -> DirectXOwner
BackendSnapshot -> MetalOwner
BackendSnapshot -> SoftwareOracle
Engine2DFacade -> CommonRenderRecord
VulkanOwner -> CommonRenderRecord
DirectXOwner -> CommonRenderRecord
MetalOwner -> CommonRenderRecord
SoftwareOracle -> CommonRenderRecord
RenderDocCLI -> CaptureEvidenceAdapter
CaptureEvidenceAdapter -> EquivalenceGate
CommonRenderRecord -> EquivalenceGate
PixelOracle -> EquivalenceGate
EquivalenceGate -> AggregateChecker
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.architecture hash=sha256:auto
Web fixtures -> production web facade -> Engine2D facade -> backend snapshot
Primitive fixtures ------------------------------^              |
                                                                 v
Vulkan / DirectX / Metal / software owners -> common record -> equivalence gate
RenderDoc CLI -> capture evidence ------------------------------^
Independent pixel oracle ---------------------------------------^
Equivalence gate -> canonical aggregate checker
```

</details>
<!-- sdn-diagram:end -->

## Module Plan

| Module | Path | Responsibility | State |
|---|---|---|---|
| Record model | `src/lib/common/renderdoc/backend_render_record.spl` | Schema constants, structs, enums, errors, semantic projection | New |
| Validation | `src/lib/common/renderdoc/backend_render_validation.spl` | Ordered fail-closed structural/provenance/reference/readback validation | New |
| Canonical form | `src/lib/common/renderdoc/backend_render_canonical.spl` | Stable field order, length-prefix serialization, SHA-256, explicit allowlist | New |
| Diff | `src/lib/common/renderdoc/backend_render_diff.spl` | Exact + semantic field walk, first/all differences | New |
| Equivalence | `src/lib/common/renderdoc/backend_render_equivalence.spl` | Independent producer/completion/handle/oracle/pairwise gate | New |
| Common exports | `src/lib/common/renderdoc/mod.spl`, `__init__.spl` | Narrow public record API | New |
| Snapshot contract | `src/lib/gc_async_mut/gpu/engine2d/backend.spl` | Opt-in backend snapshot method and honest unsupported result | Modified |
| Engine facade adapter | `src/lib/gc_async_mut/gpu/engine2d/backend_render_record_capture.spl` | `capture_backend_render_record`; requested/actual lane metadata | New |
| Backend owners | `backend_{vulkan,directx,metal,software}.spl` | Actual pipeline/resource/command/transition/completion/readback snapshot | Modified |
| Facade | `src/lib/gc_async_mut/gpu/engine2d/engine.spl`, `mod.spl` | Preserve request/translation provenance; expose capture without backend construction | Modified |
| Web adapter | `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl` | Production-facade capture request/result | Modified |
| Noalloc receipt | `src/lib/nogc_async_mut_noalloc/baremetal/common/backend_render_receipt.spl` | Fixed-field header/events/trailer suitable for serial or memory sink | New |
| SimpleOS evidence | `src/lib/common/renderdoc/simpleos_render_target_evidence.spl` | Portable QEMU/board identity, boot, display, capture, and correlation record | New |
| SimpleOS adapter | `src/os/compositor/engine2d_render_evidence.spl` | Map facade framebuffer/virtio-GPU presentation into portable receipt events | New |
| QMP adapter | `src/os/compositor/qemu_capture.spl` | Sole pure-Simple host capture path; correlate serial run/frame IDs | Modified |
| Board catalog | `src/os/port/simpleos_board_hardening.spl` | Board identity/boot contract and fail-closed physical evidence | Modified |
| SIMD target evidence | `src/lib/common/renderdoc/simpleos_simd_render_evidence.spl` | Architecture, features, provider, vector width, hits/fallbacks, instruction proof | New |
| Noalloc SIMD kernels | `src/lib/nogc_async_mut_noalloc/baremetal/{x86_64,arm64,riscv64}/engine2d_simd.spl` | Target-native fill/copy/blend/scroll vector paths | New |
| SimpleOS SIMD adapter | `src/os/compositor/engine2d_simd_evidence.spl` | Select target kernel, count execution, emit receipt evidence | New |
| Runtime SIMD owner | `src/runtime/runtime_simd_dispatch.c` | Per-ISA/per-operation vector-chunk counters beside real vector loops | Modified |
| Hosted SIMD facade | `src/lib/nogc_sync_mut/gpu/engine2d/{simd_kernels,simd_provider}.spl` | Typed counter snapshot; wrapper attempts remain separate | Modified |
| Strict CPU SIMD facade | `src/lib/gc_async_mut/gpu/engine2d/{backend_cpu,engine}.spl` | Strict `cpu_simd_x86/arm/riscv` creation and honest fallback | Modified |
| QEMU/board entry | `examples/09_embedded/simple_os/arch/common/engine2d_backend_equivalence.spl` plus arch entrypoints | Render deterministic guest scene and emit receipt | New/Modified |
| Capture evidence | `src/app/test/renderdoc_replay_inspect.spl` | Process-facade invocation of repo RenderDoc CLI; replay-open/action evidence | New |
| Capture helper | `test/helpers/renderdoc_capture_helper.shs` | Compatibility entrypoint delegating to canonical evidence tool | New |
| Aggregate | `scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs` | Bounded profile orchestration, timings/RSS, blockers, artifact rows | New |
| Existing wrappers | `scripts/{lib,tool,check}/renderdoc-*`, platform render-log wrappers | Consume record/replay fields; reject magic-only and synthetic evidence | Modified |

## Public-to-Next-Layer API

| API | Purpose |
|---|---|
| `validate_backend_render_record(record) -> Result<BackendRenderRecord, BackendRenderRecordError>` | Return only a fully valid record. |
| `canonical_backend_render_record(record, mode) -> Result<text, BackendRenderRecordError>` | Stable exact or semantic serialization. |
| `compare_backend_render_records(expected, actual) -> BackendRenderRecordDiff` | Preserve exact and semantic differences. |
| `verify_backend_render_equivalence(left, right, oracle) -> BackendRenderEquivalenceResult` | Apply all independent correctness gates. |
| `capture_backend_render_record(engine, request) -> Result<BackendRenderRecord, BackendRenderRecordError>` | Facade-only backend capture. |
| `RenderBackend.backend_render_snapshot(request) -> Result<BackendRenderSnapshot, BackendRenderRecordError>` | Backend-private evidence boundary. |
| `backend_render_receipt_begin/event/end(...)` | Bounded guest/board event protocol with no host dependency. |

## Dependency and Hot-Path Rules

`common.renderdoc` → `common.crypto.sha256`; backend capture → common schema; Engine2D/web adapters → backend capture; scripts/app inspector → IO/process facades and canonical tools. No reverse edges or cycles. Recording, canonicalization, and replay are off the ordinary frame path; intensive corpus scans occur once in the aggregate, never per request. Record schema/version changes invalidate all stored baselines and capture-derived comparisons.

Freestanding SimpleOS imports the noalloc receipt/SIMD facade, not hosted GC Engine2D. Runtime SIMD changes are owner-boundary work justified by the proven ambiguity of wrapper counters and missing per-operation execution proof; raw SIMD externs remain inside the existing no-GC sync owner.

## Requirement Coverage

| Requirements | Owners |
|---|---|
| REQ-001..004 | common record/validation/canonical/diff/equivalence |
| REQ-005..008 | Engine2D facade, snapshots, platform lane contract |
| REQ-009 | Simple replay inspector + canonical RenderDoc helpers |
| REQ-010..012 | modern SSpec/web adapters/corpora |
| REQ-013 | aggregate checker |
| REQ-014..015 | manuals, guides, cooperative verification |
| REQ-016..019 | noalloc receipt, target evidence, SimpleOS/QMP adapters, board catalog/entries and evidence specs |
| REQ-020..021 | target-specific noalloc SIMD kernels, SIMD evidence, QEMU launch/build/disassembly gates |
