# Metal Smoke Specification

> <details>

<!-- sdn-diagram:id=metal_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metal_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metal_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metal_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Smoke Specification

## Scenarios

### Metal Engine2D smoke tests

#### probe

#### reports the real Metal API and shader format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_metal()
expect(probe.requested_name).to_equal("metal")
expect(probe.api_name).to_equal("metal")
expect(probe.shader_format).to_equal("msl")
```

</details>

#### reports macOS as unavailable on non-macOS hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not is_macos():
    val probe = probe_metal()
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.feature_gate).to_equal("macos")
```

</details>

#### device readback

#### initializes the real Metal backend when macOS is available

- var backend = MetalBackend create
   - Expected: backend.init(16, 16) is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var backend = MetalBackend.create()
    expect(backend.init(16, 16)).to_equal(true)
    backend.shutdown()
```

</details>

#### reads back rendered Metal pixels when macOS is available

- var backend = MetalBackend create
   - Expected: backend.init(16, 16) is true
- backend clear
- backend draw rect filled
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixels.len() equals `256`
   - Expected: readback.pixels[0] equals `background`
   - Expected: readback.pixels[4 + (4 * 16)] equals `foreground`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var backend = MetalBackend.create()
    expect(backend.init(16, 16)).to_equal(true)
    val background = 0xFF102030 as u32
    val foreground = 0xFF405060 as u32
    backend.clear(background)
    backend.draw_rect_filled(4, 4, 4, 4, foreground)
    val readback = backend.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.pixels.len()).to_equal(256)
    expect(readback.pixels[0]).to_equal(background)
    expect(readback.pixels[4 + (4 * 16)]).to_equal(foreground)
    backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/metal_smoke_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal Engine2D smoke tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
