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
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Renderer Backend Parity Specification

## Scenarios

### Simple web renderer 2D-backend parity

#### invalid viewport

#### fails closed before Engine2D creation

The pixel and readback entrypoints reject a zero dimension before creating an
Engine2D surface; readback reports an empty `unavailable` result.

```simple
expect(simple_web_render_html_to_pixels_with_engine2d_backend(sample_html(), 0, 32, "software").len()).to_equal(0)
val readback = simple_web_render_html_to_readback_with_engine2d_backend(sample_html(), 48, 0, "software")
expect(readback.pixels.len()).to_equal(0)
expect(readback.source).to_equal("unavailable")
```

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

#### generic layout pixels stay identical for cpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val cpu = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cpu")
expect(first_mismatch_index(sw, cpu)).to_equal(-1)
```

</details>

#### generic layout pixels stay identical for cpu_simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val cpu_simd = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cpu_simd")
expect(first_mismatch_index(sw, cpu_simd)).to_equal(-1)
```

</details>

#### generic layout pixels stay identical for metal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val metal = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "metal")
expect(first_mismatch_index(sw, metal)).to_equal(-1)
```

</details>

#### generic layout pixels stay identical for cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val cuda = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "cuda")
expect(first_mismatch_index(sw, cuda)).to_equal(-1)
```

</details>

#### generic layout pixels stay identical for opencl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val opencl = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "opencl")
expect(first_mismatch_index(sw, opencl)).to_equal(-1)
```

</details>

#### generic layout pixels stay identical for vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "software")
val vulkan = simple_web_render_html_to_pixels_with_engine2d_backend(generic_layout_html(), 48, 32, "vulkan")
expect(first_mismatch_index(sw, vulkan)).to_equal(-1)
```

</details>

#### real backend selection

#### preserves supported Engine2D backend names before renderer fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_resolved_engine2d_backend_name(48, 32, "cuda")).to_equal("cuda")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "opencl")).to_equal("opencl")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "vulkan")).to_equal("vulkan")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "metal")).to_equal("metal")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "cpu_simd")).to_equal("cpu_simd")
expect(simple_web_resolved_engine2d_backend_name(48, 32, "not-a-backend")).to_equal("software")
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
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
