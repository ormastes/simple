# Web Renderer Backend Parity Specification

> <details>

<!-- sdn-diagram:id=web_renderer_backend_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_renderer_backend_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_renderer_backend_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_renderer_backend_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Renderer Backend Parity Specification

## Scenarios

### Simple web renderer 2D-backend parity

#### framebuffer output

#### software backend renders a full framebuffer with multiple colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val px = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "software")
expect(px.len()).to_equal(48 * 32)
expect(count_distinct(px)).to_be_greater_than(1)
```

</details>

#### cross-backend parity

#### cpu-backed pixels match software-backed exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "software")
val cpu = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "cpu")
expect(pixels_equal(sw, cpu)).to_equal(true)
```

</details>

#### metal-backed pixels match software-backed exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "software")
val mt = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "metal")
expect(pixels_equal(sw, mt)).to_equal(true)
```

</details>

#### generic layout pixels stay identical across preserved Engine2D backend names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cpu"))).to_equal(true)
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cpu_simd"))).to_equal(true)
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "metal"))).to_equal(true)
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cuda"))).to_equal(true)
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "opencl"))).to_equal(true)
expect(pixels_equal(sw, simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "vulkan"))).to_equal(true)
```

</details>

#### real backend selection

#### preserves supported Engine2D backend names before renderer fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_resolved_engine2d_backend_name(48, 32, "cuda")).to_equal("cuda")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "opencl")).to_equal("opencl")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "vulkan")).to_equal("vulkan")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "metal")).to_equal("metal")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "hip")).to_equal("rocm")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "cpu_simd")).to_equal("cpu_simd")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "not-a-backend")).to_equal("software")
```

</details>

#### maps preferred aliases to Engine2D preferred selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = simple_web_resolved_engine2d_backend_name(48, 32, "preferred")
expect(expected == "metal" or expected == "cuda" or expected == "rocm" or expected == "qualcomm" or expected == "vulkan" or expected == "opencl" or expected == "opengl" or expected == "intel" or expected == "webgpu" or expected == "software" or expected == "cpu_simd" or expected == "cpu").to_equal(true)
expect(simple_web_resolved_engine2d_backend_name(48, 32, "preferred")).to_equal(expected)
expect(simple_web_resolved_engine2d_backend_name(48, 32, "auto")).to_equal(expected)
expect(simple_web_resolved_engine2d_backend_name(48, 32, "default")).to_equal(expected)
expect(simple_web_resolved_engine2d_backend_name(48, 32, "")).to_equal(expected)
```

</details>

#### uses the preferred Engine2D route for default pure-Simple rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_px = simple_web_render_html_to_pixels(sample_html(), 48, 32)
val preferred_px = simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 48, 32, "preferred")
val pure_simple = web_render_backend("pure_simple", 48, 32)
expect(pixels_equal(default_px, preferred_px)).to_equal(true)
expect(pure_simple.resolved_engine2d_backend_name()).to_equal(simple_web_resolved_engine2d_backend_name(48, 32, "preferred"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple web renderer 2D-backend parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
