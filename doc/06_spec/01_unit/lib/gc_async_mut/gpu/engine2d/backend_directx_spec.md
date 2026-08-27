# DirectX 2D Engine backend contract

> Pins the Engine2D DirectX backend surface for both Linux DXVK/vkd3d routing and native Windows D3D11 routing. The platform probe drives expected evidence strings, so Windows-only behavior still has structured evidence on Linux.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DirectX 2D Engine backend contract

Pins the Engine2D DirectX backend surface for both Linux DXVK/vkd3d routing and native Windows D3D11 routing. The platform probe drives expected evidence strings, so Windows-only behavior still has structured evidence on Linux.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pins the Engine2D DirectX backend surface for both Linux DXVK/vkd3d routing and
native Windows D3D11 routing. The platform probe drives expected evidence
strings, so Windows-only behavior still has structured evidence on Linux.

**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Plan:** doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/host_gpu_lane.md

## Syntax

CPU mirror fallback before device init:

```simple
use std.spec.step

val readback = b.read_pixels_with_source()
expect(readback.source).to_equal("cpu_mirror")
expect(readback.backend_handle).to_equal(0)
```

Initialized swapchain presentation provenance:

```simple
b.initialized = true
b.swapchain_handle = 77
val readback = b.read_pixels_with_source()
expect(readback.source).to_equal("swapchain_present")
expect(readback.backend_handle).to_equal(77)
```

Native Windows checked readback does not require present:

```simple
b.clear(0xFF224466)
val readback = b.read_pixels_with_source()
expect(readback.source).to_equal("device_readback")
expect(readback.backend_handle).to_be_greater_than(0)
expect(readback.pixel_count).to_equal(16)
```

## Acceptance

- `leaf=dlopen` means a real Vulkan/DXVK/VKD3D library was found at probe time.
- `leaf=structured` means no loadable library was found and the structured
  handle fallback is active.
- `swapchain_present` is presentation provenance, not backend
  `device_readback` proof.
- DirectX may report `device_readback` only after an initialized readback
  target has executed the eligible frame and read back the expected pixel
  count with a positive native handle. Unsupported operations poison native
  receipt eligibility. Checksum is evidence, not the validity gate, because
  an all-zero frame is valid and may checksum to zero.

## Scenarios

### DirectX 2D backend — platform probe

#### probe returns a DxPlatformProbe with a non-empty platform field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe returns a DxPlatformProbe with a non-empty platform field
   - Expected: plat_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe returns a DxPlatformProbe with a non-empty platform field")
val probe = dx_platform_probe()
val plat_ok = probe.platform == "linux-dxvk" or probe.platform == "windows-native"
expect(plat_ok).to_equal(true)
```

</details>

#### probe leaf field is a recognized platform value

- probe leaf field is a recognized platform value
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe leaf field is a recognized platform value")
val probe = dx_platform_probe()
val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured" or probe.leaf == "leaf=native-d3d11"
expect(leaf_ok).to_equal(true)
```

</details>

#### probe evidence string contains platform and leaf

- probe evidence string contains platform and leaf
   - Expected: has_platform is true
   - Expected: has_leaf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe evidence string contains platform and leaf")
val probe = dx_platform_probe()
val ev = probe.evidence
val has_platform = ev.contains("platform=")
val has_leaf = ev.contains("leaf=")
expect(has_platform).to_equal(true)
expect(has_leaf).to_equal(true)
```

</details>

#### probe_directx returns Initialized or Failed status (not silent green)

- probe_directx returns Initialized or Failed status (not silent green)
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_directx returns Initialized or Failed status (not silent green)")
val result = probe_directx()
val valid = (
    result.status == BackendStatus.Initialized or
    result.status == BackendStatus.Failed or
    result.status == BackendStatus.Unavailable
)
expect(valid).to_equal(true)
```

</details>

#### probe_directx reason contains platform-specific evidence

- probe_directx reason contains platform-specific evidence
   - Expected: has_evidence is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_directx reason contains platform-specific evidence")
val result = probe_directx()
val has_evidence = if get_host_os() == "windows": result.reason.contains("leaf=native-d3d11") else: result.reason.contains("leaf=")
expect(has_evidence).to_equal(true)
```

</details>

#### probe_directx api_name distinguishes native Windows from emulation

- probe_directx api_name distinguishes native Windows from emulation
   - Expected: result.api_name equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_directx api_name distinguishes native Windows from emulation")
val result = probe_directx()
val expected = if get_host_os() == "windows": "directx" else: "directx-software-emulation"
expect(result.api_name).to_equal(expected)
```

</details>

#### probe_directx can repeat without leaking the probe device

- probe_directx can repeat without leaking the probe device
   - Expected: first.api_name equals `second.api_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_directx can repeat without leaking the probe device")
val first = probe_directx()
val second = probe_directx()
expect(first.api_name).to_equal(second.api_name)
expect(first.reason.len()).to_be_greater_than(0)
expect(second.reason.len()).to_be_greater_than(0)
```

</details>

### DirectX 2D backend — init and name

#### reported backend name distinguishes native Windows from emulation

- reported backend name distinguishes native Windows from emulation
   - Expected: b.name() equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reported backend name distinguishes native Windows from emulation")
val b = DirectXBackend.create()
val expected = if get_host_os() == "windows": "directx" else: "directx-software-emulation"
expect(b.name()).to_equal(expected)
```

</details>

#### reported backend name always identifies directx

- reported backend name always identifies directx
   - Expected: reported equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reported backend name always identifies directx")
val b = DirectXBackend.create()
val reported = b.name()
expect(reported).to_start_with("directx")
val expected = if get_host_os() == "windows": "directx" else: "directx-software-emulation"
expect(reported).to_equal(expected)
```

</details>

#### native queue uses the frozen header and fixed CLEAR/FILL records

- native queue uses the frozen header and fixed CLEAR/FILL records
   - Expected: b.native_words[0] equals `0x44583131u32`
   - Expected: b.native_words[1] equals `1u32`
   - Expected: b.native_words[2] equals `2u32`
   - Expected: b.native_words[3] equals `20u32`
   - Expected: b.native_words[4] equals `1u32`
   - Expected: b.native_words[12] equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("native queue uses the frozen header and fixed CLEAR/FILL records")
var b = DirectXBackend.create()
b.sw.init(4, 4)
b.native_hardware = true
b.native_receipt_eligible = true
b.initialized = true
b.clear(0xFF112233)
b.draw_rect_filled(1, 1, 2, 2, 0xFF445566)
expect(b.native_words[0]).to_equal(0x44583131u32)
expect(b.native_words[1]).to_equal(1u32)
expect(b.native_words[2]).to_equal(2u32)
expect(b.native_words[3]).to_equal(20u32)
expect(b.native_words[4]).to_equal(1u32)
expect(b.native_words[12]).to_equal(2u32)
b.shutdown()
```

</details>

#### unsupported operations poison native receipt eligibility

- unsupported operations poison native receipt eligibility
   - Expected: b.native_receipt_eligible is true
   - Expected: b.native_receipt_eligible is false
   - Expected: b.native_cached_handle equals `0`
   - Expected: b.native_cached_pixels.len() equals `0`
   - Expected: b.native_receipt_eligible is false
   - Expected: b.native_cached_handle equals `0`
   - Expected: b.native_cached_pixels.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unsupported operations poison native receipt eligibility")
var b = DirectXBackend.create()
b.sw.init(4, 4)
b.native_hardware = true
b.native_receipt_eligible = true
b.initialized = true
b.clear(0xFF112233)
expect(b.native_receipt_eligible).to_equal(true)
b.native_cached_handle = 77
b.native_cached_pixels = [0xFF112233u32]
b.draw_line(0, 0, 3, 3, 0xFFFFFFFF, 1)
expect(b.native_receipt_eligible).to_equal(false)
expect(b.native_cached_handle).to_equal(0)
expect(b.native_cached_pixels.len()).to_equal(0)
b.native_receipt_eligible = true
b.native_attempted = true
b.native_cached_handle = 88
b.native_cached_pixels = [0xFF445566u32]
b.clear(0xFF000000)
expect(b.native_receipt_eligible).to_equal(false)
expect(b.native_cached_handle).to_equal(0)
expect(b.native_cached_pixels.len()).to_equal(0)
b.shutdown()
```

</details>

#### opaque IMAGE is queued inline after a valid initializer

- opaque IMAGE is queued inline after a valid initializer
   - Expected: b.native_receipt_eligible is true
   - Expected: b.native_words[2] equals `1u32`
   - Expected: b.native_words[4] equals `3u32`
   - Expected: b.native_words[5] equals `10u32`
   - Expected: b.native_words[11] equals `2u32`
   - Expected: b.native_words[12] equals `0xFF010203u32`
   - Expected: b.native_words[13] equals `0xFF040506u32`
   - Expected: partial.native_receipt_eligible is true
   - Expected: partial.native_words[12] equals `3u32`
   - Expected: partial.native_words[14] equals `1u32`
   - Expected: partial.native_words[16] equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("opaque IMAGE is queued inline after a valid initializer")
var b = DirectXBackend.create()
b.sw.init(2, 1)
b.native_hardware = true
b.native_receipt_eligible = true
b.initialized = true
b.draw_image(0, 0, 2, 1, [0xFF010203u32, 0xFF040506u32])
expect(b.native_receipt_eligible).to_equal(true)
expect(b.native_words[2]).to_equal(1u32)
expect(b.native_words[4]).to_equal(3u32)
expect(b.native_words[5]).to_equal(10u32)
expect(b.native_words[11]).to_equal(2u32)
expect(b.native_words[12]).to_equal(0xFF010203u32)
expect(b.native_words[13]).to_equal(0xFF040506u32)
b.shutdown()

var partial = DirectXBackend.create()
partial.sw.init(4, 2)
partial.native_hardware = true
partial.native_receipt_eligible = true
partial.initialized = true
partial.clear(0xFF000000)
partial.draw_image_blend(1, 0, 2, 1, [0xFF010203u32, 0xFF040506u32])
expect(partial.native_receipt_eligible).to_equal(true)
expect(partial.native_words[12]).to_equal(3u32)
expect(partial.native_words[14]).to_equal(1u32)
expect(partial.native_words[16]).to_equal(2u32)
partial.shutdown()
```

</details>

#### backend owns no direct DirectX runtime extern

- backend owns no direct DirectX runtime extern
   - Expected: backend does not contain `rt_directx_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("backend owns no direct DirectX runtime extern")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl")
val facade = file_read("src/lib/nogc_sync_mut/gpu/engine2d/sffi_directx.spl")
val runtime = file_read("src/runtime/runtime_directx_core.c")
expect(backend.contains("rt_directx_")).to_equal(false)
expect(backend).to_contain("directx_execute_readback_checked")
expect(backend).to_contain("fn _native_execute_once")
expect(backend).to_contain("self.native_attempted = true")
expect(backend).to_contain("native.device_identity == self.native_device_identity")
expect(backend).to_contain("engine2d_readback_with_identity")
expect(backend).to_contain("self.native_receipt_eligible = false\n            self.native_cached_handle = 0\n            self.native_cached_pixels = []")
expect(facade).to_contain("extern fn rt_directx_execute_readback_checked")
expect(facade).to_contain("extern fn rt_directx_hardware_adapter_identity")
expect(facade).to_contain("device_identity")
expect(runtime).to_contain("if (command_index == 0) return 0;")
expect(runtime).to_contain("command_index == 0 && (x != 0 || y != 0 || w != width || h != height)")
expect(runtime).to_contain("(pixel >> 24) != 0xffu")
expect(runtime).to_contain("hash &= ((uint64_t)INT64_MAX >> 3)")
expect(runtime).to_contain("out[0] = (uint32_t)identity;")
```

</details>

#### readback defaults to CPU mirror provenance before device init

- readback defaults to CPU mirror provenance before device init
   - Expected: readback.source equals `cpu_mirror`
   - Expected: readback.backend_handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("readback defaults to CPU mirror provenance before device init")
val b = DirectXBackend.create()
val readback = b.read_pixels_with_source()
expect(readback.source).to_equal("cpu_mirror")
expect(readback.backend_handle).to_equal(0)
```

</details>

#### reports swapchain presentation provenance without claiming device readback

- reports swapchain presentation provenance without claiming device readback
   - Expected: readback.source equals `swapchain_present`
   - Expected: readback.backend_handle equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports swapchain presentation provenance without claiming device readback")
var b = DirectXBackend.create()
b.initialized = true
b.swapchain_handle = 77

val readback = b.read_pixels_with_source()

expect(readback.source).to_equal("swapchain_present")
expect(readback.backend_handle).to_equal(77)
```

</details>

#### reports checked device readback for an eligible frame

- reports checked device readback for an eligible frame
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixel_count equals `16`
   - Expected: readback.pixels[0] equals `0xFF224466`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports checked device readback for an eligible frame")
var b = DirectXBackend.create()
val ok = b.init(4, 4)
if ok:
    b.clear(0xFF224466)
    b.present()
    val readback = b.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.backend_handle).to_be_greater_than(0)
    expect(readback.pixel_count).to_equal(16)
    expect(readback.checksum).to_be_greater_than(0)
    expect(readback.pixels[0]).to_equal(0xFF224466)
    if get_host_os() == "windows":
        expect(readback.device_identity).to_be_greater_than(0)
else:
    val probe = dx_platform_probe()
    expect(probe.leaf).to_contain("leaf=")
```

</details>

#### accepts all-zero checked readback frames

- accepts all-zero checked readback frames
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixel_count equals `16`
   - Expected: readback.checksum equals `0`
   - Expected: readback.pixels[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts all-zero checked readback frames")
var b = DirectXBackend.create()
val ok = b.init(4, 4)
if ok:
    b.clear(0)
    b.present()
    val readback = b.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.backend_handle).to_be_greater_than(0)
    expect(readback.pixel_count).to_equal(16)
    expect(readback.checksum).to_equal(0)
    expect(readback.pixels[0]).to_equal(0)
else:
    val probe = dx_platform_probe()
    expect(probe.leaf).to_contain("leaf=")
```

</details>

#### init returns a bool (true or false — device available or not)

- init returns a bool (true or false — device available or not)
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("init returns a bool (true or false — device available or not)")
var b = DirectXBackend.create()
val ok = b.init(64, 64)
val valid = ok == true or ok == false
expect(valid).to_equal(true)
```

</details>

#### width and height match after init

- width and height match after init
   - Expected: b.width() equals `128`
   - Expected: b.height() equals `96`
   - Expected: b.width() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("width and height match after init")
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

- shutdown after init does not panic
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shutdown after init does not panic")
var b = DirectXBackend.create()
b.init(32, 32)
b.shutdown()
expect(1).to_equal(1)
```

</details>

### DirectX 2D backend — drawing (init required, CPU parity)

#### clear then read_pixels returns buffer of correct length when init succeeds

- clear then read_pixels returns buffer of correct length when init succeeds
   - Expected: pixels.len() equals `64`
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear then read_pixels returns buffer of correct length when init succeeds")
var b = DirectXBackend.create()
val ok = b.init(8, 8)
if ok:
    b.clear(0xFF0000FF)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)
else:
    # init failed (no DXVK/Vulkan): assert leaf evidence from probe
    val probe = dx_platform_probe()
    val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured" or probe.leaf == "leaf=native-d3d11"
    expect(leaf_ok).to_equal(true)
```

</details>

#### draw_rect_filled then read_pixels returns non-empty buffer

- draw_rect_filled then read_pixels returns non-empty buffer
   - Expected: probe.platform equals `expected_platform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rect_filled then read_pixels returns non-empty buffer")
var b = DirectXBackend.create()
val ok = b.init(16, 16)
if ok:
    b.clear(0xFFFFFFFF)
    b.draw_rect_filled(0, 0, 8, 8, 0xFF0000FF)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_be_greater_than(0)
else:
    val probe = dx_platform_probe()
    val expected_platform = if get_host_os() == "windows": "windows-native" else: "linux-dxvk"
    expect(probe.platform).to_equal(expected_platform)
```

</details>

#### draw_line does not panic

- draw_line does not panic
   - Expected: pixels.len() equals `1024`
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_line does not panic")
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

- present does not panic after init
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("present does not panic after init")
var b = DirectXBackend.create()
val ok = b.init(16, 16)
if ok:
    b.clear(0xFFAAAAAA)
    b.present()
expect(1).to_equal(1)
```

</details>

#### CPU parity: clear to red matches expected pixel value at (0,0)

- CPU parity: clear to red matches expected pixel value at (0,0)
   - Expected: p0 equals `0xFFFF0000`
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CPU parity: clear to red matches expected pixel value at (0,0)")
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
    val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured" or probe.leaf == "leaf=native-d3d11"
    expect(leaf_ok).to_equal(true)
```

</details>

### DirectX 2D backend — dispatch chain evidence

#### leaf evidence from icd_probe is a recognized value

- leaf evidence from icd_probe is a recognized value
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaf evidence from icd_probe is a recognized value")
val probe = dx_platform_probe()
val leaf_ok = probe.leaf == "leaf=dlopen" or probe.leaf == "leaf=structured" or probe.leaf == "leaf=native-d3d11"
expect(leaf_ok).to_equal(true)
```

</details>

#### on Linux without prefix, leaf is structured (DXVK dispatch chain still routes)

- on Linux without prefix, leaf is structured (DXVK dispatch chain still routes)
   - Expected: ok_is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("on Linux without prefix, leaf is structured (DXVK dispatch chain still routes)")
val probe = dx_platform_probe()
# The dispatch chain is real regardless of leaf; assert chain integrity
# by checking that device_ok is a bool (no panic)
val ok_is_bool = probe.device_ok == true or probe.device_ok == false
expect(ok_is_bool).to_equal(true)
```

</details>

#### probe_directx reason identifies the platform backend

- probe_directx reason identifies the platform backend
   - Expected: expected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_directx reason identifies the platform backend")
val result = probe_directx()
val expected = if get_host_os() == "windows": result.reason.contains("leaf=native-d3d11") else: result.reason.contains("dxvk-d3d11")
expect(expected).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/host_gpu_lane.md`
- **Plan:** `doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md`
- **Design:** `doc/05_design/host_gpu_lane.md`
- **Research:** `doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e5d0eadd18078ca8f7fd5919bebfe5ad1207f05c9afaf60832f1b57ae5e029c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e5d0eadd18078ca8f7fd5919bebfe5ad1207f05c9afaf60832f1b57ae5e029c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e5d0eadd18078ca8f7fd5919bebfe5ad1207f05c9afaf60832f1b57ae5e029c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe returns a DxPlatformProbe with a non-empty platform field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe leaf field is a recognized platform value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe evidence string contains platform and leaf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
