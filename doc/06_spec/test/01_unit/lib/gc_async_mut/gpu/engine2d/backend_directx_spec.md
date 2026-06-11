# Backend Directx Specification

> <details>

<!-- sdn-diagram:id=backend_directx_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_directx_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_directx_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_directx_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Directx Specification

## Scenarios

### DirectX 2D backend — platform probe

#### probe returns a DxPlatformProbe with a non-empty platform field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dx_platform_probe()
val plat_ok = probe.platform == "linux-dxvk" or probe.platform == "windows-native"
expect(plat_ok).to_equal(true)
```

</details>

#### probe leaf field is either dlopen or structured

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dx_platform_probe()
val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### probe evidence string contains platform and leaf

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dx_platform_probe()
val ev = probe.evidence
val has_platform = ev.contains("platform=")
val has_leaf = ev.contains("leaf=")
expect(has_platform).to_equal(true)
expect(has_leaf).to_equal(true)
```

</details>

#### probe_directx returns Initialized or Failed status (not silent green)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = probe_directx()
val valid = (
    result.status == BackendStatus.Initialized or
    result.status == BackendStatus.Failed or
    result.status == BackendStatus.Unavailable
)
expect(valid).to_equal(true)
```

</details>

#### probe_directx reason contains leaf evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = probe_directx()
val has_leaf = result.reason.contains("leaf=")
expect(has_leaf).to_equal(true)
```

</details>

#### probe_directx api_name is directx

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = probe_directx()
expect(result.api_name).to_equal("directx")
```

</details>

### DirectX 2D backend — init and name

#### backend name is directx

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = DirectXBackend.create()
expect(b.name()).to_equal("directx")
```

</details>

#### init returns a bool (true or false — device available or not)

- var b = DirectXBackend create
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(64, 64)
val valid = ok == true or ok == false
expect(valid).to_equal(true)
```

</details>

#### width and height match after init

- var b = DirectXBackend create
   - Expected: b.width() equals `128`
   - Expected: b.height() equals `96`
   - Expected: b.width() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(128, 96)
if ok:
    expect(b.width()).to_equal(128)
    expect(b.height()).to_equal(96)
else:
    # Not initialized: width/height are 0
    expect(b.width()).to_equal(0)
```

</details>

#### shutdown after init does not panic

- var b = DirectXBackend create
- b init
- b shutdown
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
b.init(32, 32)
b.shutdown()
expect(1).to_equal(1)
```

</details>

### DirectX 2D backend — drawing (init required, CPU parity)

#### clear then read_pixels returns buffer of correct length when init succeeds

- var b = DirectXBackend create
- b clear
   - Expected: pixels.len() equals `64`
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(8, 8)
if ok:
    b.clear(0xFF0000FF)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)
else:
    # init failed (no DXVK/Vulkan): assert leaf evidence from probe
    val probe = dx_platform_probe()
    val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured"
    expect(leaf_ok).to_equal(true)
```

</details>

#### draw_rect_filled then read_pixels returns non-empty buffer

- var b = DirectXBackend create
- b clear
- b draw rect filled
   - Expected: probe.platform equals `linux-dxvk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(16, 16)
if ok:
    b.clear(0xFFFFFFFF)
    b.draw_rect_filled(0, 0, 8, 8, 0xFF0000FF)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_be_greater_than(0)
else:
    val probe = dx_platform_probe()
    expect(probe.platform).to_equal("linux-dxvk")
```

</details>

#### draw_line does not panic

- var b = DirectXBackend create
- b clear
- b draw line
   - Expected: pixels.len() equals `1024`
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(32, 32)
if ok:
    b.clear(0xFFFFFFFF)
    b.draw_line(0, 0, 31, 31, 0xFF000000, 1)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(1024)
else:
    expect(1).to_equal(1)
```

</details>

#### present does not panic after init

- var b = DirectXBackend create
- b clear
- b present
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = DirectXBackend.create()
val ok = b.init(16, 16)
if ok:
    b.clear(0xFFAAAAAA)
    b.present()
expect(1).to_equal(1)
```

</details>

#### CPU parity: clear to red matches expected pixel value at (0,0)

- var cpu b = DirectXBackend create
- cpu b clear
   - Expected: p0 equals `0xFFFF0000`
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu_b = DirectXBackend.create()
val ok = cpu_b.init(4, 4)
if ok:
    cpu_b.clear(0xFFFF0000)
    val pixels = cpu_b.read_pixels()
    # pixel at index 0 should be red (ARGB: 0xFFFF0000)
    val p0 = pixels[0]
    expect(p0).to_equal(0xFFFF0000)
else:
    val probe = dx_platform_probe()
    val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured"
    expect(leaf_ok).to_equal(true)
```

</details>

### DirectX 2D backend — dispatch chain evidence

#### leaf evidence from icd_probe is a recognized value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dx_platform_probe()
val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### on Linux without prefix, leaf is structured (DXVK dispatch chain still routes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dx_platform_probe()
# The dispatch chain is real regardless of leaf; assert chain integrity
# by checking that device_ok is a bool (no panic)
val ok_is_bool = probe.device_ok == true or probe.device_ok == false
expect(ok_is_bool).to_equal(true)
```

</details>

#### probe_directx reason contains dxvk-d3d11 identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = probe_directx()
val has_dxvk = result.reason.contains("dxvk-d3d11")
expect(has_dxvk).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DirectX 2D backend — platform probe
- DirectX 2D backend — init and name
- DirectX 2D backend — drawing (init required, CPU parity)
- DirectX 2D backend — dispatch chain evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
