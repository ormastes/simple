# Shared macOS GPU 2D Draw IR and event fixture

> Defines the backend-independent scene and semantic transition consumed by the separate Vulkan and Metal live lanes. The focus flag supplied here is synthetic semantic input: this integration spec does not create a native window, observe a platform event, execute either GPU backend, or provide live rendering proof.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared macOS GPU 2D Draw IR and event fixture

Defines the backend-independent scene and semantic transition consumed by the separate Vulkan and Metal live lanes. The focus flag supplied here is synthetic semantic input: this integration spec does not create a native window, observe a platform event, execute either GPU backend, or provide live rendering proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/engine2d_four_backend_capture.md |
| Plan | doc/03_plan/sys_test/engine2d_four_backend_capture.md |
| Design | doc/05_design/engine2d_four_backend_capture.md |
| Research | doc/01_research/local/engine2d_four_backend_capture.md |
| Source | `test/02_integration/rendering/macos_gpu_2d_draw_ir_event_fixture_spec.spl` |
| Updated | 2026-07-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Defines the backend-independent scene and semantic transition consumed by the
separate Vulkan and Metal live lanes. The focus flag supplied here is synthetic
semantic input: this integration spec does not create a native window, observe
a platform event, execute either GPU backend, or provide live rendering proof.

The fixture freezes equal 3840x2160 geometry at 300 DPI, Draw IR command
identity, 24-point-to-100-pixel vector-text sizing, and the expected canonical
focus transition. Live wrappers must independently prove that a real native
focus receipt caused the same transition.

**Requirements:** doc/02_requirements/feature/engine2d_four_backend_capture.md
**Plan:** doc/03_plan/sys_test/engine2d_four_backend_capture.md
**Design:** doc/05_design/engine2d_four_backend_capture.md
**Research:** doc/01_research/local/engine2d_four_backend_capture.md
**Architecture:** doc/04_architecture/engine2d_four_backend_capture.md

## Syntax

```sh
bin/simple test test/02_integration/rendering/macos_gpu_2d_draw_ir_event_fixture_spec.spl --mode=interpreter
```

## Expected Result

The deterministic composition and synthetic semantic reducer contract pass.
The negative scenario confirms that absent native-focus input cannot claim a
focus reduction or active-state mutation. No live Vulkan or Metal run is
claimed by this spec.

## Scenarios

### shared macOS Vulkan/Metal Draw IR and semantic-event fixture

#### freezes one backend-neutral composition at 300 DPI

- Build the shared backend-neutral 300-DPI fixture
- Verify frozen Draw IR geometry and command identity
- Verify vector-text point-to-pixel sizing
   - Expected: fixture.dpi equals `MACOS_GPU_2D_FIXTURE_DPI`
   - Expected: fixture.composition.composition_id equals `macos-gpu-2d-frozen-composition-v1`
   - Expected: fixture.composition.scene_key equals `macos-gpu-2d-frozen-scene-v1`
   - Expected: fixture.composition.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: fixture.composition.batches.len() equals `1`
   - Expected: fixture.composition.batches[0].commands.len() equals `5`
   - Expected: fixture.width equals `MACOS_GPU_2D_FIXTURE_WIDTH`
   - Expected: fixture.height equals `MACOS_GPU_2D_FIXTURE_HEIGHT`
   - Expected: MACOS_GPU_2D_FIXTURE_WIDTH equals `3840`
   - Expected: MACOS_GPU_2D_FIXTURE_HEIGHT equals `2160`
   - Expected: embedding.x equals `0`
   - Expected: embedding.y equals `0`
   - Expected: embedding.width equals `MACOS_GPU_2D_FIXTURE_WIDTH`
   - Expected: embedding.height equals `MACOS_GPU_2D_FIXTURE_HEIGHT`
   - Expected: embedding.opacity_milli equals `1000`
   - Expected: _command_kind("macos-gpu-2d-background") equals `DRAW_IR_COMMAND_RECT`
   - Expected: _command_kind("macos-gpu-2d-title") equals `DRAW_IR_COMMAND_TEXT`
   - Expected: MACOS_GPU_2D_FIXTURE_FONT_PIXELS equals `100`
   - Expected: _command_style_value(component_id, "font-size") equals `100`
   - Expected: _command_style_value(component_id, "line-height") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the shared backend-neutral 300-DPI fixture")
step("Verify frozen Draw IR geometry and command identity")
step("Verify vector-text point-to-pixel sizing")
val fixture = macos_gpu_2d_draw_ir_event_fixture(
    true, MACOS_GPU_2D_NATIVE_FOCUS_KIND)
expect(fixture.dpi).to_equal(MACOS_GPU_2D_FIXTURE_DPI)
expect(fixture.composition.composition_id).to_equal("macos-gpu-2d-frozen-composition-v1")
expect(fixture.composition.scene_key).to_equal("macos-gpu-2d-frozen-scene-v1")
expect(fixture.composition.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(fixture.composition.batches.len()).to_equal(1)
expect(fixture.composition.batches[0].commands.len()).to_equal(5)
val embedding = fixture.composition.batches[0].embedding
expect(fixture.width).to_equal(MACOS_GPU_2D_FIXTURE_WIDTH)
expect(fixture.height).to_equal(MACOS_GPU_2D_FIXTURE_HEIGHT)
expect(MACOS_GPU_2D_FIXTURE_WIDTH).to_equal(3840)
expect(MACOS_GPU_2D_FIXTURE_HEIGHT).to_equal(2160)
expect(embedding.x).to_equal(0)
expect(embedding.y).to_equal(0)
expect(embedding.width).to_equal(MACOS_GPU_2D_FIXTURE_WIDTH)
expect(embedding.height).to_equal(MACOS_GPU_2D_FIXTURE_HEIGHT)
expect(embedding.opacity_milli).to_equal(1000)
expect(_command_kind("macos-gpu-2d-background")).to_equal(DRAW_IR_COMMAND_RECT)
expect(_command_kind("macos-gpu-2d-title")).to_equal(DRAW_IR_COMMAND_TEXT)
expect(MACOS_GPU_2D_FIXTURE_FONT_PIXELS).to_equal(100)
for component_id in [
    "macos-gpu-2d-title",
    "macos-gpu-2d-action-label"
]:
    expect(_command_style_value(component_id, "font-size")).to_equal("100")
    expect(_command_style_value(component_id, "line-height")).to_equal("100")
```

</details>

#### reduces an observed native focus event through canonical UIEvent

- Supply deterministic synthetic native-focus input
- Reduce it through the shared canonical semantic fixture
- Compare the Vulkan and Metal lane expectations
   - Expected: vulkan_fixture.mutation.event_name equals `metal_fixture.mutation.event_name`
   - Expected: vulkan_fixture.mutation.event_name equals `focus`
   - Expected: vulkan_fixture.mutation.native_focus_observed is true
   - Expected: vulkan_fixture.mutation.native_focus_reduced is true
   - Expected: vulkan_fixture.mutation.before_focus equals `macos-gpu-2d-root`
   - Expected: vulkan_fixture.mutation.after_focus equals `macos-gpu-2d-action`
   - Expected: vulkan_fixture.mutation.changed is true
   - Expected: vulkan_fixture.mutation.after_accent equals `MACOS_GPU_2D_ACTIVE_ACCENT`
   - Expected: metal_fixture.mutation.after_accent equals `vulkan_fixture.mutation.after_accent`
   - Expected: _command_color("macos-gpu-2d-action") equals `MACOS_GPU_2D_ACTIVE_ACCENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Supply deterministic synthetic native-focus input")
step("Reduce it through the shared canonical semantic fixture")
step("Compare the Vulkan and Metal lane expectations")
val vulkan_fixture = macos_gpu_2d_draw_ir_event_fixture(
    true, MACOS_GPU_2D_NATIVE_FOCUS_KIND)
val metal_fixture = macos_gpu_2d_draw_ir_event_fixture(
    true, MACOS_GPU_2D_NATIVE_FOCUS_KIND)
expect(vulkan_fixture.mutation.event_name).to_equal(metal_fixture.mutation.event_name)
expect(vulkan_fixture.mutation.event_name).to_equal("focus")
expect(vulkan_fixture.mutation.native_focus_observed).to_equal(true)
expect(vulkan_fixture.mutation.native_focus_reduced).to_equal(true)
expect(vulkan_fixture.mutation.before_focus).to_equal("macos-gpu-2d-root")
expect(vulkan_fixture.mutation.after_focus).to_equal("macos-gpu-2d-action")
expect(vulkan_fixture.mutation.changed).to_equal(true)
expect(vulkan_fixture.mutation.after_accent).to_equal(MACOS_GPU_2D_ACTIVE_ACCENT)
expect(metal_fixture.mutation.after_accent).to_equal(vulkan_fixture.mutation.after_accent)
expect(_command_color("macos-gpu-2d-action")).to_equal(MACOS_GPU_2D_ACTIVE_ACCENT)
```

</details>

#### does not claim reduction or active composition without native focus

- Build the fixture without native-focus input
- Require the idle focus and accent state to remain unchanged
   - Expected: fixture.mutation.native_focus_observed is false
   - Expected: fixture.mutation.native_focus_reduced is false
   - Expected: fixture.mutation.changed is false
   - Expected: fixture.mutation.after_focus equals `macos-gpu-2d-root`
   - Expected: fixture.mutation.after_accent equals `MACOS_GPU_2D_IDLE_ACCENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the fixture without native-focus input")
step("Require the idle focus and accent state to remain unchanged")
val fixture = macos_gpu_2d_draw_ir_event_fixture(
    false, MACOS_GPU_2D_NATIVE_FOCUS_KIND)
expect(fixture.mutation.native_focus_observed).to_equal(false)
expect(fixture.mutation.native_focus_reduced).to_equal(false)
expect(fixture.mutation.changed).to_equal(false)
expect(fixture.mutation.after_focus).to_equal("macos-gpu-2d-root")
expect(fixture.mutation.after_accent).to_equal(MACOS_GPU_2D_IDLE_ACCENT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/engine2d_four_backend_capture.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_four_backend_capture.md`
- **Design:** `doc/05_design/engine2d_four_backend_capture.md`
- **Research:** `doc/01_research/local/engine2d_four_backend_capture.md`


</details>
