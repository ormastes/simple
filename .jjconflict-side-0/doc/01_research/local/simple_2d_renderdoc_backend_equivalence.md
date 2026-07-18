<!-- codex-research -->
# Simple 2D RenderDoc Backend Equivalence — Local Research

The repository has strong readback, pixel-oracle, platform-aggregate, and capture-launch pieces, but no detailed backend-render record or field comparator. Two legacy “RenderDoc functional” specs are simulated and contain placeholder passes. Current Linux DirectX evidence is CPU rasterization plus structured host arrays, not DXVK rendering, and must not report device readback.

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.research hash=sha256:auto render=ascii
@layout dag
@direction LR

WebFixtures -> WebRenderFacade
PrimitiveFixtures -> Engine2DFacade
WebRenderFacade -> Engine2DFacade
Engine2DFacade -> VulkanBackend
Engine2DFacade -> DirectXEmulation
Engine2DFacade -> MetalOrVulkanTranslation
VulkanBackend -> BackendReadback
DirectXEmulation -> BackendReadback
MetalOrVulkanTranslation -> BackendReadback
RenderDocCapture -> RDCArtifact
BackendReadback -> MissingDetailedRecord
RDCArtifact -> MissingDetailedRecord
MissingDetailedRecord -> MissingStructuredDiff
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Existing Evidence

| Area | Evidence | Finding |
|---|---|---|
| Readback contract | `src/lib/gc_async_mut/gpu/engine2d/backend.spl:3-55` | Pixels, source, handle, count, checksum and typed source exist; format/stride/frame/provenance do not. |
| Facade selection | `src/lib/gc_async_mut/gpu/engine2d/engine.spl:193-290` | Strict Vulkan plus explicit `directx-on-vulkan`/`metal-on-vulkan` names are reusable. |
| Vulkan internals | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:148-202` | Framebuffer, shader, pipeline, clip, and session state are private and not recorded. |
| DirectX truth | `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl:129-176,257-282` | Draws use `SoftwareBackend`; host-array output is incorrectly labeled `device_readback`. |
| DX translation readiness | `build/dx/prefix/dx_prefix_readiness.json:1-8` | DXVK/vkd3d libraries exist, but Wine/runtime submission is absent. |
| Coarse render log | `scripts/lib/render-log-common.shs:187-284` | `simple-render-log-v1` has viewport/artifact/checksum; detailed native state is opaque text. |
| Pixel oracle | `scripts/check/check-vulkan-engine2d-readback.shs:259-438` | Exact independent formulas, present/readback, and zero mismatch exist; provenance is incomplete. |
| Capture helpers | `scripts/tool/renderdoc-evidence.shs:13-44`; `scripts/lib/renderdoc-evidence-common.shs:458-490` | Canonical lanes exist, but validation stops at four-byte `RDOC` magic. |
| Capture hole | `test/03_system/check/renderdoc_simple_gate_spec.spl:101-123` | A fabricated `RDOCsynthetic` file is deliberately accepted. |
| Legacy trace specs | `test/03_system/check/gpu_rendering_{renderdoc_capture_functional,vulkan_renderdoc_capture}_spec.spl` | Simulated constants, forbidden boolean wrappers, unconditional Metal/DirectX passes, nonexistent covered module. |
| Web corpus | `tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt:1-51` | 50 production layout cases; text AA is honestly tracked as divergent. |
| Broad corpus | `src/app/wm_compare/site_corpus.spl:14-103` | 132 deterministic offline famous-site fixtures are reusable. |
| Widget fixture | `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html:7-216` | 43 widgets plus layout/clipping/media coverage. |
| Modern SSpec model | `test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl:57-102` | Structured layout/diff evidence and readable steps are reusable patterns. |

## Reusable Modules and Gaps

- Reuse `Engine2D.create_requested_backend`, `Engine2DReadback`, `ReadbackSource`, production web-render facade, Draw IR diff/layout, exact ARGB comparison, canonical capture launchers, and native platform aggregates.
- Add the missing versioned detailed record, validation, deterministic serialization, field diff, RenderDoc-open/replay inspection, and equivalence gate.
- Add the referenced-but-missing `test/helpers/renderdoc_capture_helper.shs`; keep app/spec code behind facades.
- Linux host evidence: NVIDIA TITAN RTX + RTX A6000, Mesa llvmpipe, Vulkan layer, repo RenderDoc 1.44, and three existing `RDOC` artifacts. Native Metal/DirectX remain external-host checkpoints.
- Open questions: NONE; “Vulkan emulation infra of Metal/DirectX” is interpreted as explicit Vulkan translation/emulation lanes whose provenance must never be called native Metal/DirectX.

## Cooperative Review

Read-only sidecars audited RenderDoc/schema, web/SSpec coverage, and Linux backend feasibility. Primary Codex reconciled their findings and rejected simulated, magic-only, same-path, and mislabeled-device evidence.

