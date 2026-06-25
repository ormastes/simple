# Webgpu Strict Specification

> <details>

<!-- sdn-diagram:id=webgpu_strict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_strict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_strict_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_strict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Strict Specification

## Scenarios

### WebGPU strict smoke tests

#### probe_webgpu diagnostics

#### probe_webgpu returns a typed BackendProbeResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
val ok = probe.is_ok() or status_is_terminal_failure(probe)
expect(ok).to_equal(true)
```

</details>

#### probe_webgpu reports requested_name as webgpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
expect(probe.requested_name).to_equal("webgpu")
```

</details>

#### probe_webgpu on unavailable carries non-empty fallback_reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if not probe.is_ok():
    expect(probe.fallback_reason).to_not_equal("")
```

</details>

#### probe_webgpu diagnostic_text is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
val txt = probe.diagnostic_text()
expect(txt.len()).to_be_greater_than(0)
```

</details>

#### default build — webgpu-real feature off

#### probe_webgpu returns Unavailable status when feature gate is off

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if not probe.is_ok():
    expect(probe.status).to_equal(BackendStatus.Unavailable)
```

</details>

#### probe_webgpu feature_gate mentions webgpu-real when unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if not probe.is_ok():
    expect(probe.feature_gate).to_equal("webgpu-real")
```

</details>

#### probe_webgpu fallback_reason is non-empty when unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if not probe.is_ok():
    expect(probe.fallback_reason).to_not_equal("")
```

</details>

#### probe_webgpu selected_name is cpu when unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if not probe.is_ok():
    expect(probe.selected_name).to_equal("cpu")
```

</details>

#### webgpu-real enabled — off-screen adapter smoke

#### probe_webgpu reports success when adapter is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if probe.is_ok():
    expect(probe.selected_name).to_equal("webgpu")
    expect(probe.shader_format).to_equal("wgsl")
```

</details>

#### create_with_backend_strict succeeds and returns Engine2D when adapter present

1. var engine = result unwrap
2. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "webgpu")
    expect(result.is_ok()).to_equal(true)
    var engine = result.unwrap()
    engine.shutdown()
```

</details>

#### off-screen texture upload and readback returns 16x16 pixel buffer

1. var engine = result unwrap
2. engine clear
3. engine draw rect filled
4. engine present
   - Expected: pixels.len() equals `256`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "webgpu")
    if result.is_ok():
        var engine = result.unwrap()
        engine.clear(color_red_u32())
        engine.draw_rect_filled(4, 4, 8, 8, color_green_u32())
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        engine.shutdown()
```

</details>

#### corner pixels are red after clear with red

1. var engine = result unwrap
2. engine clear
3. engine present
   - Expected: pixels[0] equals `color_red_u32()`
   - Expected: pixels[255] equals `color_red_u32()`
4. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_webgpu()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "webgpu")
    if result.is_ok():
        var engine = result.unwrap()
        engine.clear(color_red_u32())
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels[0]).to_equal(color_red_u32())
        expect(pixels[255]).to_equal(color_red_u32())
        engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/webgpu_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGPU strict smoke tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
