<!-- codex-design -->
# Simple 2D RenderDoc Backend Equivalence Detail Design

## Data Model

| Type | Essential fields |
|---|---|
| `BackendRenderProducer` | kind, stable producer ID, evidence hash, capture/log paths |
| `BackendExecutionProvenance` | requested/actual backend, native API, execution kind, translation layer, adapter/device/driver, fallback reason, handle |
| `BackendRenderTarget` | width, height, format, stride, sample count, content hash |
| `BackendRenderPipeline` | stable ID/kind, pipeline/shader/fixed-state hashes |
| `BackendRenderResource` | stable ID/kind/hash/size/format |
| `BackendRenderBinding` | command, pipeline/resource IDs, set/binding, range/access |
| `BackendRenderCommand` | contiguous sequence, kind, sorted typed fields |
| `BackendRenderTransition` | sequence, resource, before/after state, stage/access |
| `BackendRenderReadback` | source, size/format/stride/count/hash/nonblank count |
| `BackendRenderRecord` | schema, producer, provenance, target/viewport/scissor, arrays above, completion, semantic/record hashes |
| `BackendRenderRecordDiff` | exact/semantic equality, first difference, all differences, allowed nondeterministic paths |
| `BackendRenderEquivalenceResult` | validations, independence, completion/handles, nonblank, oracle/pair mismatches, tolerance flag, stable reason |

## Validation Order

1. Schema name/version and required lowercase SHA-256 values.
2. Positive dimensions, bounded rectangles, format/stride/pixel-count agreement.
3. Requested/actual/native API/execution/translation/readback matrix consistency.
4. Completed frame, positive handle, nonempty contiguous command sequence.
5. Unique IDs, resolved references/bindings, valid resource transition chains.
6. Readback matches target, is nonblank, and its content hash recomputes.
7. Semantic and exact hashes recompute from canonical field walks.

Stable errors include `unsupported-version`, `missing-field`, `invalid-enum`, `invalid-dimensions`, `invalid-stride`, `invalid-hash`, `invalid-handle`, `incomplete-frame`, `empty-command-stream`, `invalid-sequence`, `duplicate-id`, `dangling-reference`, `contradictory-provenance`, `invalid-transition`, `invalid-readback`, `blank-readback`, `non-independent-producers`, and `oracle-mismatch`.

## Canonicalization and Comparison

Never iterate maps. Sort pipeline/resource/binding IDs and command fields explicitly; retain validated command/transition sequence; encode values with path + type + length prefix. Exact mode walks every field. Semantic mode walks target, viewport/scissor, canonical pipelines/resources/bindings/commands/transitions, completion, and readback content while classifying producer/provenance differences rather than erasing them. Hashes are corroboration after the field walk, never the equality oracle.

The v1 normalization allowlist contains only capture/log path prefixes. It cannot normalize API/backend/adapter/device/driver, execution/translation, handle positivity, completion, pipeline/shader/resource hashes, commands, transitions, dimensions/format/stride, readback source, or pixels.

## Capture Sequence

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.sequence -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.sequence hash=sha256:auto render=ascii
@layout dag
@direction LR
Fixture -> ProductionFacade
ProductionFacade -> RequestedBackend
RequestedBackend -> RecordSnapshot
RequestedBackend -> PresentReadback
RequestedBackend -> RenderDocCapture
RenderDocCapture -> ReplayOpen
RecordSnapshot -> ValidateRecord
PresentReadback -> AbsoluteOracle
ReplayOpen -> CaptureEvidence
ValidateRecord -> CompareRecords
AbsoluteOracle -> CompareRecords
CaptureEvidence -> CompareRecords
CompareRecords -> AggregateRow
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.sequence hash=sha256:auto
fixture -> facade -> requested backend -> snapshot -> validate --+
                                  |-> present/readback -> oracle --+-> compare -> row
                                  `-> RenderDoc -> replay-open -----+
```

</details>
<!-- sdn-diagram:end -->

## Platform Matrix

| Lane | Required truth | Linux outcome |
|---|---|---|
| `linux-vulkan-nvidia-native` | actual/native API Vulkan; physical NVIDIA adapter; device readback; positive handle | Required for intensive PASS when host exposes NVIDIA |
| `linux-vulkan-mesa-software` | actual/native API Vulkan; lavapipe/llvmpipe software adapter; honest software-device label | Required separate lane |
| `linux-directx-request-vulkan-compat` | requested DirectX, actual Vulkan, translated, `simple-directx-on-vulkan` | Compatibility only; never DXVK/native D3D |
| `linux-metal-request-vulkan-compat` | requested Metal, actual Vulkan, translated, `simple-metal-on-vulkan` | Compatibility only; never native Metal/MoltenVK |
| Windows D3D11/D3D12 | actual/native D3D, native staging readback, PIX/debug content evidence | `host_unavailable` on Linux |
| macOS Metal | actual/native Metal, completed command buffer, device readback, Xcode capture evidence | `host_unavailable` on Linux |
| SimpleOS x86_64/RV64 QEMU | guest-native facade, framebuffer/virtio-GPU handle, serial receipt, QMP nonblank exact capture | Required QEMU profile |
| Physical board | same receipt protocol plus real board/image/flash/boot/capture/transcript identity | External; never inferred from QEMU |

## SimpleOS QEMU and Board Receipt

The guest cannot depend on RenderDoc, host processes, or filesystem scans. A fixed-field `BackendRenderReceipt` header and ordered `BackendRenderReceiptEvent` stream records schema version, architecture, requested/actual renderer code, execution kind, framebuffer/GPU handle, target geometry/format/stride, contiguous command/event sequence, resource/state hashes, completion, pixel/checksum evidence, and stable reason codes. A noalloc serial/memory sink emits header/events/trailer; the host parser expands it into `BackendRenderRecord` and rejects missing, duplicate, reordered, truncated, or contradictory events.

QEMU must boot the actual SimpleOS image/ELF, wait for the guest completion trailer, capture through the existing QMP harness (not inline Python), decode PPM through Simple helpers, and compare exact anchors plus full checksum/nonblank/dimensions against an independent scene oracle. Ten fresh boots must produce the same semantic receipt and pixels. For framebuffer-write-only paths, the receipt honestly labels guest readback unavailable and the QMP capture as the independent external readback; it does not call QMP pixels `device_readback`.

A physical-board row additionally requires architecture, vendor/model/revision/serial, image hash, flash/download command, reset/boot path, renderer/backend, positive framebuffer/GPU handle, completion trailer, capture mechanism, exact hash/nonblank/dimensions, and serial or SSH transcript. Without those fields the row is `source_present` or `qemu_verified`.

`SimpleOsRenderTargetEvidence` nests in the common record and carries runtime (`qemu` or `physical-board`), board/firmware/boot identity, architecture/SoC/display controller, driver/scanout/resource IDs, DMA/cache/IOMMU mode, framebuffer facts, positive handle, present sequence/fence/completion, guest receipt/readback, serial log/hash, external capture path/hash/tool/version, run/frame correlation, oracle hash, and mismatch count. x86_64, RV64, and ARM64 use the same shape.

Existing false-green paths are removed: `engine2d_in_qemu_spec.spl` may not invoke inline Python or accept 95% similarity/auto-baselines; VirtIO init failure is a failed or host-unavailable gate, not success; RV64 fixed strings and ARM64 static metadata are insufficient. `src/os/compositor/qemu_capture.spl` is the sole QMP adapter and must correlate the live serial receipt, firmware hash, run ID, frame ID, and captured framebuffer.

## SimpleOS SIMD Rendering

`SimpleOsSimdRenderEvidence` records guest architecture, required/detected feature, selected provider, vector width, implementation/instruction family, per-operation native hits for fill/copy/alpha/scroll, scalar fallback counts and reason, scalar/SIMD hashes, mismatch count, and firmware/run/frame identity. The x86 row requires SSE2 and, when the QEMU CPU exposes it, AVX2; AArch64 requires NEON; RV64 launches with the V extension and records RVV vector length. Unsupported QEMU CPU features are fail-closed `host_unavailable`, not scalar PASS.

Each operation uses `CpuSimdKernelEvidence(operation, dispatch_calls, vector_chunks, vector_lanes, scalar_tail_pixels, scalar_fallback_calls, output_hash, fallback_reason)`. Runtime-owner counters increment only inside SSE2/AVX2/NEON/RVV vector loops; Simple wrapper/provider hit counters remain diagnostic and cannot satisfy execution. The current single ambiguous hit counter is replaced by per-ISA/per-operation snapshots, including AArch64 blend and x86/RVV operations required by the scene.

Each guest executes scalar and target-vector implementations over independent buffers, then the selected SIMD provider renders the verification scene. PASS requires positive native hits for every required operation, zero fallback for the required path, zero scalar/SIMD mismatches, matching QMP pixels, and expected target instruction-family evidence from the guest ELF. Existing x86 `NOP*` SIMD runtime shims, host reports, provider names, or same-arithmetic helper labels cannot satisfy this gate.

Hosted `Engine2D.create_requested_backend` gains strict `cpu_simd_x86`, `cpu_simd_arm`, and `cpu_simd_riscv` lanes. ISA mismatch or zero vector chunks returns typed unavailable; generic `cpu_simd` may fall back only while reporting actual backend `cpu` and a nonempty reason. SimpleOS uses the freestanding noalloc facade and never imports hosted GC Engine2D.

## RenderDoc Evidence

The pure-Simple inspector invokes the repo-local `renderdoccmd` through `app.io` process facades to prove the capture opens/replays and to collect stable CLI markers/logs. The in-application backend snapshot provides detailed semantic pipeline/resource/command/transition state. Capture validation requires non-synthetic artifact provenance, real file size beyond a header, `RDOC` precheck, replay-open success, API/device agreement, relevant action markers from the capture session, and agreement with the in-app record/readback. Unsupported CLI detail remains an explicit evidence limitation, not fabricated state.

## Profiles and Observability

- `focused`: schema/diff negatives, one surface per family, one strict Vulkan lane, six layouts, 12 stratified sites, whole widget DOM fixture; ≤15 minutes.
- `intensive`: all 50 layouts, all 132 once through production reference plus 24 stratified cross-backend, whole 43-widget fixture plus 12 isolated widgets, and 100-frame stress; ≤60 minutes.
- `qualification`: every site/widget per backend plus native Windows/macOS; scheduled external profile.

Every aggregate row reports status/reason, requested/actual/native API, execution/translation, adapter/driver, handle/completion/readback, record/artifact/log paths, exact/semantic diff counts, oracle/pair mismatch counts, tolerance flag, elapsed milliseconds, max RSS, and REQ IDs. Missing timing/RSS fails NFR evidence.

## Error Handling and Runtime Decision

No new raw `rt_*`, env, process, backend-field poke, or synthetic-handle shortcut is allowed outside owners. `runtime_need`: per-ISA/per-operation actual vector-loop counters and missing required vector operations; `facade_checked`: existing SIMD no-GC sync owner, `app.io`, Engine2D facade, existing RenderDoc helper; `chosen_path`: runtime-owned SIMD counters plus smallest owner facades, otherwise reuse facade; `rejected_shortcuts`: wrapper-hit-as-execution, NOP stubs, host/C-harness substitution, Python replay implementation, magic-only acceptance, CPU mirror labeled device, fixture-painted references, and runtime-local aliases.
