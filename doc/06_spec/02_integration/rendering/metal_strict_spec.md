# Metal Strict Specification

> <details>

<!-- sdn-diagram:id=metal_strict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metal_strict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metal_strict_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metal_strict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Strict Specification

## Scenarios

### Metal strict smoke tests

#### probe_metal() platform diagnostics

#### always returns a BackendProbeResult (never panics)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = probe_metal()
# Just confirm we got a result — any status is valid
val status_text = result.diagnostic_text()
expect(status_text.len()).to_be_greater_than(0)
```

</details>

#### on Linux: status is Unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = probe_metal()
    expect(result.status == BackendStatus.Unavailable).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: reason contains 'macOS'

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = probe_metal()
    expect(result.fallback_reason.contains("macOS")).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: feature gate is 'macos'

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = probe_metal()
    expect(result.feature_gate).to_equal("macos")
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: requested_name is 'metal'

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = probe_metal()
    expect(result.requested_name).to_equal("metal")
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on macOS: probe_metal returns initialized or failed (not unavailable)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_macos():
    val result = probe_metal()
    val not_unavailable = result.status != BackendStatus.Unavailable
    expect(not_unavailable).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### Engine2D.create_with_backend_strict metal

#### always returns a Result (never panics)

- var engine = result unwrap
   - Expected: engine.width() equals `16`
- engine shutdown
   - Expected: diag.requested_name equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Engine2D.create_with_backend_strict(16, 16, "metal")
if result.is_ok():
    var engine = result.unwrap()
    expect(engine.width()).to_equal(16)
    engine.shutdown()
else:
    val diag = result.unwrap_err()
    expect(diag.requested_name).to_equal("metal")
```

</details>

#### on Linux: returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    expect(result.is_ok()).to_equal(false)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: Err carries BackendProbeResult with Unavailable status

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.status == BackendStatus.Unavailable).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: Err reason contains 'macOS'

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.fallback_reason.contains("macOS")).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on macOS: returns Ok or typed failed diagnostic

- var engine = result unwrap
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`
- engine shutdown
   - Expected: diag.status == BackendStatus.Failed is true
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        expect(engine.width()).to_equal(16)
        expect(engine.height()).to_equal(16)
        engine.shutdown()
    else:
        val diag = result.unwrap_err()
        expect(diag.status == BackendStatus.Failed).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### macOS Metal rendering smoke (draw + readback)

#### on macOS: clear sets all pixels to given color

- var engine = result unwrap
- engine clear
- engine present
- engine shutdown
   - Expected: all_red is true
   - Expected: diag.status == BackendStatus.Failed is true
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(4, 4, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        val red = rgb(255, 0, 0)
        engine.clear(red)
        engine.present()
        val pixels = engine.read_pixels()
        var all_red = true
        var i = 0
        while i < 16:
            if pixels[i] != red:
                all_red = false
            i = i + 1
        engine.shutdown()
        expect(all_red).to_equal(true)
    else:
        val diag = result.unwrap_err()
        expect(diag.status == BackendStatus.Failed).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### on macOS: draw_rect_filled produces non-zero pixels in region

- var engine = result unwrap
- engine clear
- engine draw rect filled
- engine present
- engine shutdown
   - Expected: top_left equals `blue`
   - Expected: diag.status == BackendStatus.Failed is true
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        engine.clear(0u32)
        val blue = rgb(0, 0, 255)
        engine.draw_rect_filled(0, 0, 8, 8, blue)
        engine.present()
        val pixels = engine.read_pixels()
        # Top-left pixel (0,0) should be blue
        val top_left = pixels[0]
        engine.shutdown()
        expect(top_left).to_equal(blue)
    else:
        val diag = result.unwrap_err()
        expect(diag.status == BackendStatus.Failed).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### on macOS: CPU backend and Metal produce same clear result

- var cpu engine = Engine2D create with backend
- cpu engine clear
- cpu engine present
- cpu engine shutdown
- var metal engine = metal result unwrap
- metal engine clear
- metal engine present
- metal engine shutdown
   - Expected: parity is true
   - Expected: diag.status == BackendStatus.Failed is true
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if os_is_macos():
    val metal_result = Engine2D.create_with_backend_strict(4, 4, "metal")
    var cpu_engine = Engine2D.create_with_backend(4, 4, "cpu")
    val green = rgb(0, 255, 0)
    cpu_engine.clear(green)
    cpu_engine.present()
    val cpu_pixels = cpu_engine.read_pixels()
    cpu_engine.shutdown()

    if metal_result.is_ok():
        var metal_engine = metal_result.unwrap()
        metal_engine.clear(green)
        metal_engine.present()
        val metal_pixels = metal_engine.read_pixels()
        metal_engine.shutdown()

        var parity = true
        var i = 0
        while i < 16:
            if metal_pixels[i] != cpu_pixels[i]:
                parity = false
            i = i + 1
        expect(parity).to_equal(true)
    else:
        val diag = metal_result.unwrap_err()
        expect(diag.status == BackendStatus.Failed).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/metal_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal strict smoke tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
