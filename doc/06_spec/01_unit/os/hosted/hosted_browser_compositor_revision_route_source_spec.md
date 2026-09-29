# Hosted Browser Compositor Revision Route Source Specification

> Tests covering hosted browser compositor production revision route source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Browser Compositor Revision Route Source Specification

## Scenarios

### hosted browser compositor production revision route source

#### treats a checksum-zero retained delta as a queued frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats a checksum-zero retained delta as a queued frame
   - Expected: delta.checksum equals `0u64`
   - Expected: delta.pixels.len() equals `0`
   - Expected: delta.damage_pixels.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("treats a checksum-zero retained delta as a queued frame")
val delta = WmContentFrame(
    window_id: "91", scene_revision: 0, content_revision: 2,
    origin_kind: WM_CONTENT_ORIGIN_SIMPLE_WEB, width: 64, height: 48,
    pixels: [], checksum: 0u64, parent_window_id: "",
    offset_x: 0, offset_y: 0, engine2d_status: "engine2d_rendered",
    engine2d_backend: "cpu_simd", engine2d_reason: "draw-ir-retained-damage",
    material_fallback_kind: "solid-material",
    material_fallback_reason: "cpu-raster-backdrop-sampling-unavailable",
    material_fallback_sha256: "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    theme_id: "default",
    theme_source_manifest_sha256: "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    base_content_revision: 1, damage_rects: [1, 1, 1, 1],
    damage_pixels: [0xff123456u32]
)
expect(delta.checksum).to_equal(0u64)
expect(delta.pixels.len()).to_equal(0)
expect(delta.damage_pixels.len()).to_equal(1)
expect(hosted_browser_renderer_frame_pending(delta)).to_be(true)
val consumed = WmContentFrame(
    window_id: "", scene_revision: 0, content_revision: 0,
    origin_kind: "", width: 0, height: 0, pixels: [], checksum: 0u64,
    parent_window_id: "", offset_x: 0, offset_y: 0
)
expect(hosted_browser_renderer_frame_pending(consumed)).to_be(false)
```

</details>

#### pins process, registry, and hosted entry to revision-aware rasterization

- pins process, registry, and hosted entry to revision-aware rasterization
   - Expected: process does not contain `render_draw_ir_composition_resources(`
   - Expected: process does not contain `render_frame()`
   - Expected: store does not contain `render_draw_ir_composition_resources(`
   - Expected: initial does not contain `render_draw_ir_composition_resources(`
   - Expected: periodic does not contain `render_draw_ir_composition_resources(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 82 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pins process, registry, and hosted entry to revision-aware rasterization")
val process = executable_source(
    "src/os/hosted/hosted_browser_renderer_process.spl"
)
val registry = executable_source(
    "src/os/hosted/hosted_browser_renderer_registry.spl"
)
val entry = executable_source("src/os/hosted/hosted_entry.spl")

expect(process).to_contain(
    "pub struct HostedBrowserRendererResult:"
)
expect(process).to_contain("composition_revision: i64")
expect(process).to_contain("image_resources: [SimpleOsHostGpuImageResource]")
expect(process).to_contain("decoded.message.generation")
expect(process).to_contain("frame.composition_revision")
expect(process.contains("render_draw_ir_composition_resources(")).to_equal(false)
expect(process.contains("render_frame()")).to_equal(false)

val store_start = registry.find("me _store_frame(")
val store_end = registry.find("me ensure(", store_start)
val store = registry.slice(store_start, store_end)
expect(store_start).to_be_greater_than(-1)
expect(store_end).to_be_greater_than(store_start)
expect(registry).to_contain(
    "HostedBrowserRendererProcess.create(generation, width, height)"
)
expect(store).to_contain(
    "raster.render_draw_ir_composition_resources_revision("
)
expect(store).to_contain(
    "raster.render_draw_ir_composition_resources_packed_damage("
)
expect(store).to_contain("result.damage_receipt.mode == DAMAGE_PLAN_LOCAL")
expect(store).to_contain("base_content_revision: entry.published_content_revision")
expect(store).to_contain("damage_rects: packed.rects, damage_pixels: packed.pixels")
expect(store).to_contain("entry.published_frame_valid")
expect(store).to_contain("entry.pending_frame.window_id == \"\"")
expect(registry).to_contain("hosted_browser_renderer_frame_pending(")
expect(store).to_contain("result.composition")
expect(store).to_contain("result.image_resources")
expect(store).to_contain("result.producer_generation")
expect(store).to_contain("result.composition_revision")
expect(store.contains("render_draw_ir_composition_resources(")).to_equal(false)

val run_start = entry.find("fn _run_hosted_wm(")
val run_end = entry.find(
    "    print \"SimpleOS shared hosted WM closed\"", run_start
)
val run = entry.slice(run_start, run_end)
val initial_start = run.find("if browser_frame_registered:")
val initial_end = run.find(
    "    if browser_profile_window_id <= 0 or not browser_renderer_ready:",
    initial_start
)
val initial = run.slice(initial_start, initial_end)
val periodic_start = run.find(
    "if browser_renderer_ready:\n            val browser_poll = browser_renderer.poll()"
)
val periodic_end = run.find(
    "            var desired_browser_width = browser_content_width",
    periodic_start
)
val periodic = run.slice(periodic_start, periodic_end)
expect(run_start).to_be_greater_than(-1)
expect(run_end).to_be_greater_than(run_start)
expect(run).to_contain(
    "var browser_renderer = HostedBrowserRendererProcess.create("
)
expect(initial_start).to_be_greater_than(-1)
expect(initial_end).to_be_greater_than(initial_start)
expect(periodic_start).to_be_greater_than(-1)
expect(periodic_end).to_be_greater_than(periodic_start)
expect(initial.split(
    "render_draw_ir_composition_resources_revision("
).len()).to_equal(2)
expect(periodic.split(
    "render_draw_ir_composition_resources_revision("
).len()).to_equal(2)
expect(initial.contains("render_draw_ir_composition_resources(")).to_equal(false)
expect(periodic.contains("render_draw_ir_composition_resources(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted browser compositor production revision route source.
- hosted browser compositor production revision route source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f74c80c6fa8dd759ab0cc8a9c9c75d053a3fcae22877fbbc40730f206f066f96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f74c80c6fa8dd759ab0cc8a9c9c75d053a3fcae22877fbbc40730f206f066f96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f74c80c6fa8dd759ab0cc8a9c9c75d053a3fcae22877fbbc40730f206f066f96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl
mirror: doc/06_spec/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a checksum-zero retained delta as a queued frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins process, registry, and hosted entry to revision-aware rasterization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
