# Engine Vulkan Font Route Specification

> Tests covering Engine2D Vulkan font routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Vulkan Font Route Specification

## Scenarios

### Engine2D Vulkan font routing

#### publishes the complete RenderBackend table before Vulkan extensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes the complete RenderBackend table before Vulkan extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("publishes the complete RenderBackend table before Vulkan extensions")
val backend_source = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl"
)
val render_impl = backend_source.index_of(
    "impl RenderBackend for VulkanBackend:"
) ?? -1
val extended_impl = backend_source.index_of(
    "impl Engine2DExtended for VulkanBackend:"
) ?? -1
expect(render_impl).to_be_greater_than(-1)
expect(extended_impl).to_be_greater_than(render_impl)
```

</details>

#### retains the original Vulkan session instead of a native method return

- retains the original Vulkan session instead of a native method return


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("retains the original Vulkan session instead of a native method return")
val backend_source = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl"
)
expect(backend_source).to_contain(
    "vulkan_backend_retain_session(self, session)"
)
expect(backend_source).to_contain("session.retain()")
expect(backend_source).to_contain("backend.session = session")
expect(backend_source.contains(
    "self.session = session.retain()"
)).to_equal(false)
expect(backend_source).to_contain(
    "me font_atlas_pipeline_evidence() -> VulkanFontPipelineEvidence:"
)
```

</details>

#### keeps non-Vulkan engines out of the Vulkan font lane

- keeps non-Vulkan engines out of the Vulkan font lane
   - Expected: engine.vulkan_backend equals `nil`
   - Expected: engine.install_vulkan_font_spirv([0u8; 20]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps non-Vulkan engines out of the Vulkan font lane")
var engine = Engine2D.create_with_backend(2, 2, "software")
expect(engine.vulkan_backend).to_equal(nil)
expect(engine.install_vulkan_font_spirv([0u8; 20])).to_equal(false)
engine.shutdown()
```

</details>

#### replays the same font batch through software after Vulkan poison

- replays the same font batch through software after Vulkan poison
   - Expected: engine.selected_backend_name equals `vulkan-poisoned-software`
   - Expected: engine.vulkan_backend != nil is true
   - Expected: engine.vulkan_backend.?.completion_unknown is true
   - Expected: engine._draw_font_batch(0, 0, batch) is true
   - Expected: batch.atlas_cache_identity() equals `identity_before`
   - Expected: engine.read_pixels()[0] equals `0xff123456u32`
   - Expected: engine.read_pixels()[63] equals `0xffabcdefu32`
   - Expected: engine.last_font_execution_target equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays the same font batch through software after Vulkan poison")
var engine = Engine2D.create_with_backend(8, 8, "software")
engine.selected_backend_name = "vulkan"
engine.vulkan_backend = Some(VulkanBackend.create())
engine.clear(0xff010203u32)
engine.draw_rect_filled(7, 7, 1, 1, 0xffabcdefu32)
val fallback_pixels = engine.read_pixels()
engine._poison_vulkan_font_surface(fallback_pixels)
expect(engine.selected_backend_name).to_equal("vulkan-poisoned-software")
expect(engine.vulkan_backend != nil).to_equal(true)
expect(engine.vulkan_backend.?.completion_unknown).to_equal(true)
val batch = FontRenderBatch(
    program_version: FONT_ATLAS_COMPOSITE_PROGRAM_VERSION,
    font_identity: "poison-replay", face_generation: 7, valid: true,
    atlas_width: 1, atlas_height: 1, atlas_pixels: [0xffffffffu32],
    quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
        width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 0xff123456u32)],
    atlas_generation: 9, dirty_rects: [])
val identity_before = batch.atlas_cache_identity()
expect(engine._draw_font_batch(0, 0, batch)).to_equal(true)
expect(batch.atlas_cache_identity()).to_equal(identity_before)
expect(engine.read_pixels()[0]).to_equal(0xff123456u32)
expect(engine.read_pixels()[63]).to_equal(0xffabcdefu32)
expect(engine.last_font_execution_target).to_equal("cpu")
engine.shutdown()
```

</details>

#### replays an unavailable Vulkan font batch through software from quad zero

- replays an unavailable Vulkan font batch through software from quad zero
   - Expected: engine._draw_font_batch(0, 0, batch) is true
   - Expected: engine.read_pixels()[4] equals `0xff123456u32`
   - Expected: engine.vulkan_font_state_unknown is false
   - Expected: unavailable != nil is true
   - Expected: unavailable.?.d_font_atlas equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays an unavailable Vulkan font batch through software from quad zero")
var engine = Engine2D.create_with_backend(3, 2, "software")
engine.vulkan_backend = Some(VulkanBackend.create())
val batch = FontRenderBatch(
    program_version: FONT_ATLAS_COMPOSITE_PROGRAM_VERSION,
    font_identity: "route-test", face_generation: 1, valid: true,
    atlas_width: 1, atlas_height: 1, atlas_pixels: [0xff000000u32],
    quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 1, dst_y: 1,
        width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 0xff123456u32)],
    atlas_generation: 1, dirty_rects: []
)
engine.clear(0xff000000u32)
expect(engine._draw_font_batch(0, 0, batch)).to_equal(true)
expect(engine.read_pixels()[4]).to_equal(0xff123456u32)
expect(engine.vulkan_font_state_unknown).to_equal(false)
val unavailable = engine.vulkan_backend
expect(unavailable != nil).to_equal(true)
expect(unavailable.?.d_font_atlas).to_equal(0)
engine.shutdown()
```

</details>

#### routes only the canonical Vulkan constructor and preserves CPU replay

- routes only the canonical Vulkan constructor and preserves CPU replay
   - Expected: source does not contain `self.vulkan_backend = vulkan`
   - Expected: source does not contain `self.vulkan_backend = vulkan_typed`
   - Expected: source does not contain `self.metal_backend = metal`
   - Expected: perf_source does not contain `engine.vulkan_backend = vulkan`
   - Expected: source.count("Engine2D(") equals `23`
   - Expected: source.count("font_owner: Engine2DFontOwner.new()") equals `23`
   - Expected: source does not contain `font_owner: Engine2DFontOwner =`
   - Expected: source does not contain `engine2d_font_owner_current`
   - Expected: source does not contain `font_renderer: FontRenderer?`
   - Expected: source does not contain `self.font_renderer =`
   - Expected: owner_source does not contain `active: FontRenderer?`
   - Expected: owner_source does not contain `Some(`
   - Expected: draw_ir_source does not contain `eng.font_renderer =`
   - Expected: live_source does not contain `engine.font_renderer =`
   - Expected: compositor_source does not contain `self.engine.font_renderer`
   - Expected: source does not contain `vulkan_backend: dx_vk`
   - Expected: source does not contain `vulkan_backend: metal_vk`
   - Expected: source does not contain `evidence.device_executed and evidence.parity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 101 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes only the canonical Vulkan constructor and preserves CPU replay")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
val owner_source = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/font_owner.spl"
)
val font_source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl")
val perf_source = file_read(
    "test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl"
)
val draw_ir_source = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl"
)
val live_source = file_read(
    "test/02_integration/rendering/macos_gpu_2d_live_harness.spl"
)
val rss_source = file_read(
    "src/app/test/shared_multilingual_gpu_fonts_rss_probe.spl"
)
val compositor_source = file_read(
    "src/os/compositor/compositor_engine2d.spl"
)
val widget_showcase_source = file_read(
    "examples/06_io/ui/widget_showcase_gui.spl"
)
val graphics_showcase_source = file_read(
    "examples/06_io/ui/graphics_2d_showcase.spl"
)
expect(source).to_contain("use std.gpu.engine2d.backend_vulkan_font")
expect(source).to_contain("vulkan_backend: VulkanBackend? = nil")
expect(source).to_contain("vulkan_backend: Some(vulkan)")
expect(source).to_contain("self.vulkan_backend = Some(vulkan)")
expect(source).to_contain("self.vulkan_backend = Some(vulkan_typed)")
expect(source.contains("self.vulkan_backend = vulkan")).to_equal(false)
expect(source.contains("self.vulkan_backend = vulkan_typed")).to_equal(false)
expect(source).to_contain(
    "if val Some(vulkan) = self.vulkan_backend:"
)
expect(source).to_contain("self.metal_backend = Some(metal)")
expect(source.contains("self.metal_backend = metal")).to_equal(false)
expect(perf_source).to_contain("engine.vulkan_backend = Some(vulkan)")
expect(perf_source).to_contain(
    "engine.vulkan_backend = Some(VulkanBackend.create())"
)
expect(perf_source.contains("engine.vulkan_backend = vulkan")).to_equal(false)
expect(source).to_contain("font_owner: Engine2DFontOwner")
expect(source.count("Engine2D(")).to_equal(23)
expect(source.count("font_owner: Engine2DFontOwner.new()")).to_equal(23)
expect(source.contains("font_owner: Engine2DFontOwner =")).to_equal(false)
expect(source).to_contain("val owner: Engine2DFontOwner = self.font_owner")
expect(source).to_contain("self.font_owner.active[0]")
expect(source).to_contain("Engine2DFontOwner(active: [FontRenderer.new()])")
expect(source).to_contain("Engine2DFontOwner(active: [renderer])")
expect(source).to_contain("engine2d_font_owner_clear(owner)")
# The owner idiom moved off Option entirely (2026-07-26): an
# Option-wrapped aggregate crossing a function boundary is the
# deterministic payload-loss shape on the freestanding native lane,
# so the owner holds a one-slot [FontRenderer] list and exposes a
# scalar presence check instead of engine2d_font_owner_current.
expect(source).to_contain("self.font_owner.active.len()")
expect(source.contains("engine2d_font_owner_current")).to_equal(false)
expect(source.contains("font_renderer: FontRenderer?")).to_equal(false)
expect(source.contains("self.font_renderer =")).to_equal(false)
expect(owner_source).to_contain("active: [FontRenderer]")
expect(owner_source.contains("active: FontRenderer?")).to_equal(false)
expect(owner_source.contains("Some(")).to_equal(false)
expect(owner_source).to_contain("fn engine2d_font_owner_store(mut owner: Engine2DFontOwner")
expect(draw_ir_source).to_contain("eng.install_font_renderer(fonts)")
expect(draw_ir_source.contains("eng.font_renderer =")).to_equal(false)
expect(live_source).to_contain("engine.install_font_renderer(loaded_fonts)")
expect(live_source.contains("engine.font_renderer =")).to_equal(false)
expect(perf_source).to_contain("engine.install_font_renderer(fixture.renderer)")
expect(rss_source).to_contain("engine.install_font_renderer(FontRenderer.new())")
expect(compositor_source).to_contain("self.engine.selected_font_identity()")
expect(compositor_source.contains("self.engine.font_renderer")).to_equal(false)
expect(widget_showcase_source).to_contain("engine.install_font_renderer(loaded_fonts)")
expect(graphics_showcase_source).to_contain("engine.install_font_renderer(loaded_fonts)")
expect(source).to_contain("last_font_execution_attempts: []")
expect(source.contains("vulkan_backend: dx_vk")).to_equal(false)
expect(source.contains("vulkan_backend: metal_vk")).to_equal(false)
expect(source).to_contain("evidence.dispatch_count == batch.quads.len()")
expect(source).to_contain("evidence.reason == \"partial-framebuffer-restore-failed\"")
expect(source).to_contain("evidence.reason == \"missing-command-cleanup-capability\"")
expect(source).to_contain("evidence.reason == \"descriptor-cleanup-failed\"")
expect(source).to_contain("evidence.reason == \"atlas-cleanup-failed\"")
expect(source).to_contain("evidence.reason == \"cleanup-failed\"")
expect(source).to_contain("evidence.reason == \"fence-completion-unknown\"")
# The promotion gate moved into backend_vulkan_font.spl: promotion
# keys on evidence.promotion_ready, never on the weaker
# device_executed+parity pair, and engine.spl stays free of the
# weaker pair entirely.
expect(font_source).to_contain("elif evidence.promotion_ready:")
expect(source.contains("evidence.device_executed and evidence.parity")).to_equal(false)
expect(source).to_contain("self.selected_backend_name = \"vulkan-poisoned-software\"")
expect(source).to_contain("self._poison_vulkan_font_surface(evidence.fallback_pixels)")
expect(font_source).to_contain("_vulkan_font_with_fallback")
expect(source).to_contain("target + \":poisoned-skip\"")
expect(source).to_contain("evidence.reason == \"device-lost\"")
expect(source).to_contain("vulkan.shutdown()")
expect(source).to_contain("if self.vulkan_font_state_unknown and target != \"cpu\"")
expect(source).to_contain("while quad_index < batch.quads.len()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Vulkan font routing.
- Engine2D Vulkan font routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eab5f402251311cad733c809bc7a4fe9a637d75baa13f9edbe9f41448672a090`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eab5f402251311cad733c809bc7a4fe9a637d75baa13f9edbe9f41448672a090`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eab5f402251311cad733c809bc7a4fe9a637d75baa13f9edbe9f41448672a090`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the complete RenderBackend table before Vulkan extensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps non-Vulkan engines out of the Vulkan font lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays the same font batch through software after Vulkan poison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
