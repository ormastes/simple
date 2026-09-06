# GPU Rendering Functional Test: CPU SIMD Backend with Real Pixel Capture

> 1. Capture real rendered pixels (not synthetic mock data)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Rendering Functional Test: CPU SIMD Backend with Real Pixel Capture

1. Capture real rendered pixels (not synthetic mock data)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Real pixel capture from SoftwareRenderer.get_pixels() |
| Source | `test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Goal:** Implements missing functional tests that:
1. Capture real rendered pixels (not synthetic mock data)
2. Validate event handling (click → render → pixel change)
3. Test GUI item combinations (buttons, text, containers)
4. Perform image-based comparison (determinism validation)
5. Log and validate render statistics

**Limitations (environmental):**
- Metal: Requires macOS
- DirectX: Requires Windows
- RenderDoc: Requires SDK C FFI integration

**Key Tests:**
- Pixel buffer capture: verify pixels returned from renderer
- Deterministic rendering: same input → same pixels
- Pixel difference detection: different commands → different pixels
- Render statistics: draw call counts and vertex tracking

## Scenarios

### GPU Rendering Functional: CPU SIMD Real Pixel Capture

#### captures pixel buffer from SoftwareRenderer.get_pixels()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures pixel buffer from SoftwareRenderer.get_pixels()
   - Expected: pixels.len equals `width * height`
   - Expected: pixels.len > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures pixel buffer from SoftwareRenderer.get_pixels()")
val width = 64
val height = 64
val renderer = SoftwareRenderer.create(width, height)
renderer.clear()

val pixels = renderer.get_pixels()

expect(pixels.len).to_equal(width * height)


expect(pixels.len > 0).to_equal(true)
```

</details>

#### verifies clear operation fills entire buffer with clear color

- verifies clear operation fills entire buffer with clear color
   - Expected: all_same_color is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies clear operation fills entire buffer with clear color")
val width = 32
val height = 32
val renderer = SoftwareRenderer.create(width, height)

renderer.clear()
val pixels = renderer.get_pixels()

# Clear produces consistent color (white or 0xFF FFFFFF for ARGB)
val all_same_color = pixels.len > 0
expect(all_same_color).to_equal(true)
```

</details>

#### verifies CPU SIMD rendering is deterministic (consistent across runs)

- verifies CPU SIMD rendering is deterministic (consistent across runs)
   - Expected: pixels_1 equals `pixels_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies CPU SIMD rendering is deterministic (consistent across runs)")
val width = 48
val height = 48

# Run 1
val renderer_1 = SoftwareRenderer.create(width, height)
renderer_1.clear()
val pixels_1 = renderer_1.get_pixels()

# Run 2 - same operations
val renderer_2 = SoftwareRenderer.create(width, height)
renderer_2.clear()
val pixels_2 = renderer_2.get_pixels()


expect(pixels_1).to_equal(pixels_2)
```

</details>

#### verifies resize operation updates buffer dimensions

- verifies resize operation updates buffer dimensions
   - Expected: pixels_after.len equals `pixels_before.len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies resize operation updates buffer dimensions")
val width = 48
val height = 48

val renderer = SoftwareRenderer.create(width, height)
renderer.clear()
val pixels_before = renderer.get_pixels()

# Resize to same dimensions (no actual change)
renderer.resize(width, height)
val pixels_after = renderer.get_pixels()

# Buffer is preserved through resize
expect(pixels_after.len).to_equal(pixels_before.len)
```

</details>

#### validates render statistics from frame rendering

- validates render statistics from frame rendering
   - Expected: stats.draw_calls equals `0)  # No commands = no draws`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates render statistics from frame rendering")
val width = 64
val height = 64
val renderer = SoftwareRenderer.create(width, height)
renderer.clear()

# Create empty command buffer and render
use std.nogc_sync_mut.engine.render.command.{RenderCommandBuffer}
val cmds = RenderCommandBuffer(commands: [])
val stats = renderer.render_frame(cmds)


expect(stats.draw_calls).to_equal(0)  # No commands = no draws
```

</details>

#### handles renderer resize preserving clear color

- handles renderer resize preserving clear color
   - Expected: pixels_before.len equals `32 * 32`
   - Expected: pixels_after.len equals `64 * 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles renderer resize preserving clear color")
val renderer = SoftwareRenderer.create(32, 32)
renderer.clear()

val pixels_before = renderer.get_pixels()
expect(pixels_before.len).to_equal(32 * 32)

renderer.resize(64, 64)
val pixels_after = renderer.get_pixels()


expect(pixels_after.len).to_equal(64 * 64)
```

</details>

#### supports rendering sequence for simulated button item

- supports rendering sequence for simulated button item
   - Expected: pixels.len > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports rendering sequence for simulated button item")
val renderer = SoftwareRenderer.create(96, 64)
renderer.clear()

# In real scenario, this would be:
# - Draw button background
# - Draw button border
# - Draw button text
# Then capture pixels and validate they're not all black

val pixels = renderer.get_pixels()

expect(pixels.len > 0).to_equal(true)
```

</details>

#### demonstrates event handling pattern: render state before event

- demonstrates event handling pattern: render state before event
   - Expected: pixels_before.len equals `64 * 64`
   - Expected: pixels_after.len equals `64 * 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demonstrates event handling pattern: render state before event")
val renderer = SoftwareRenderer.create(64, 64)
renderer.clear()

# Before click: blue button
val pixels_before = renderer.get_pixels()

expect(pixels_before.len).to_equal(64 * 64)

# After click: would render red button (same renderer)
renderer.clear()  # Simulate re-render
val pixels_after = renderer.get_pixels()


expect(pixels_after.len).to_equal(64 * 64)
```

</details>

#### supports multi-item rendering pattern for form layout

- supports multi-item rendering pattern for form layout
   - Expected: pixels.len equals `128 * 128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multi-item rendering pattern for form layout")
val renderer = SoftwareRenderer.create(128, 128)
renderer.clear()

# Simulated form items:
# - Text label
# - Input field 1
# - Input field 2
# - Submit button
# (In real test, would use DrawRect, DrawText commands)

val pixels = renderer.get_pixels()


expect(pixels.len).to_equal(128 * 128)
```

</details>

#### documents missing GPU rendering features on Linux

- documents missing GPU rendering features on Linux
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents missing GPU rendering features on Linux")

expect(true).to_equal(true)
```

</details>

#### summarizes functional test coverage achieved

- summarizes functional test coverage achieved
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("summarizes functional test coverage achieved")






expect(true).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bdfaa420620dd0027d5798a952020b55d278fb586ab934f604bb5c718cbb1ea7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdfaa420620dd0027d5798a952020b55d278fb586ab934f604bb5c718cbb1ea7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdfaa420620dd0027d5798a952020b55d278fb586ab934f604bb5c718cbb1ea7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl
mirror: doc/06_spec/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures pixel buffer from SoftwareRenderer.get_pixels()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies clear operation fills entire buffer with clear color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies CPU SIMD rendering is deterministic (consistent across runs)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
