# Browser Backend Pixel Paths Specification

> <details>

<!-- sdn-diagram:id=browser_backend_pixel_paths_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_backend_pixel_paths_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_backend_pixel_paths_spec -> std
browser_backend_pixel_paths_spec -> common
browser_backend_pixel_paths_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_backend_pixel_paths_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Backend Pixel Paths Specification

## Scenarios

### browser backend pixel hot paths

#### converts the default framebuffer to host pixels once and reuses the cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = BrowserBackend.create(4, 3, "software").unwrap()
val first = backend.pixels_rgba_i64()
expect(first.len()).to_equal(12)
expect(first[0]).to_equal(0x2D2D2D)
expect(backend.present_pixels_cache_stores).to_equal(1)
expect(backend.present_pixels_cache_hits).to_equal(0)

val second = backend.pixels_rgba_i64()
expect(second.len()).to_equal(12)
expect(second[11]).to_equal(0x2D2D2D)
expect(backend.present_pixels_cache_stores).to_equal(1)
expect(backend.present_pixels_cache_hits).to_equal(1)
```

</details>

#### serializes the framebuffer as stable P3 ppm text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = BrowserBackend.create(2, 1, "software").unwrap()
val ppm = backend.snapshot_ppm_text()
expect(ppm).to_start_with("P3\n2 1\n255\n")
expect(ppm).to_contain("45 45 45")
```

</details>

#### keeps native backend aliases available for preferred graphical lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BrowserBackend.create(8, 8, "metal").unwrap().gpu_backend()).to_equal("metal")
expect(BrowserBackend.create(8, 8, "cuda").unwrap().gpu_backend()).to_equal("cuda")
expect(BrowserBackend.create(8, 8, "hip").unwrap().gpu_backend()).to_equal("rocm")
expect(BrowserBackend.create(8, 8, "vulkan").unwrap().gpu_backend()).to_equal("vulkan")
```

</details>

#### collects wide render layout entries without dropping hit-test boxes

- text widget
- text widget
- text widget
- text widget
- text widget
- text widget
- text widget
- text widget
- backend render frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = panel("wide_layout_root", "Wide Layout", [
    text_widget("wide_layout_0", "zero"),
    text_widget("wide_layout_1", "one"),
    text_widget("wide_layout_2", "two"),
    text_widget("wide_layout_3", "three"),
    text_widget("wide_layout_4", "four"),
    text_widget("wide_layout_5", "five"),
    text_widget("wide_layout_6", "six"),
    text_widget("wide_layout_7", "seven")
])
val state = init_state(build_tree_with_title(root, "Wide Layout", "dark"))
val backend = BrowserBackend.create(120, 96, "software").unwrap()

backend.render_frame(state.tree, state)

expect(backend.layout_cache.len()).to_be_greater_than(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser backend pixel hot paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
