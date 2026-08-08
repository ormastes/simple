# Wm App Process Contract Specification

> Tests covering WM app process contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm App Process Contract Specification

## Scenarios

### WM app process contract

#### names the widget showcase source file as the executable app identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WIDGET_SHOWCASE_APP_SOURCE).to_equal("examples/06_io/ui/widget_showcase_gui.spl")
expect(WIDGET_SHOWCASE_APP_ID).to_equal("/examples/widget-showcase")
expect(WIDGET_SHOWCASE_TITLE).to_equal("Widget Showcase")
```

</details>

#### distinguishes native launch from WM client launch by mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_app_mode_is_client(WM_APP_MODE_CLIENT)).to_equal(true)
expect(wm_app_mode_is_client("")).to_equal(false)
expect(wm_app_mode_is_client("native")).to_equal(false)
```

</details>

#### round-trips the filesystem child bridge request

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = wm_widget_showcase_bridge_request(1234, "build/tmp/showcase.ppm")
val encoded = wm_fs_bridge_encode(req)
val decoded = wm_fs_bridge_decode(encoded)
expect(decoded.kind).to_equal("create_window")
expect(decoded.source_path).to_equal(WIDGET_SHOWCASE_APP_SOURCE)
expect(decoded.app_id).to_equal(WIDGET_SHOWCASE_APP_ID)
expect(decoded.title).to_equal(widget_showcase_window_title("software"))
expect(decoded.pid).to_equal(1234)
expect(decoded.frame_path).to_equal("build/tmp/showcase.ppm")
expect(decoded.event_path).to_equal("build/tmp/showcase.ppm.event")
expect(decoded.frame_seq_path).to_equal("build/tmp/showcase.ppm.seq")
expect(decoded.content).to_contain(WIDGET_SHOWCASE_APP_SOURCE)
```

</details>

#### maps backend tags to backend-stamped window title tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(showcase_backend_token("simd")).to_equal("simple_gui_simple_2d_simd")
expect(showcase_backend_token("cpu_simd")).to_equal("simple_gui_simple_2d_simd")
expect(showcase_backend_token("cpu-simd")).to_equal("simple_gui_simple_2d_simd")
expect(showcase_backend_token("simd-cpu")).to_equal("simple_gui_simple_2d_simd")
expect(showcase_backend_token("vulkan")).to_equal("simple_gui_simple_2d_vulkan")
expect(showcase_backend_token("metal")).to_equal("simple_gui_simple_2d_metal")
expect(showcase_backend_token("weird-backend")).to_equal("simple_gui_simple_2d_software")
expect(widget_showcase_window_title("metal")).to_contain("gui_showcase_backed_simple_gui_simple_2d_metal")
val backend_req = wm_widget_showcase_bridge_request_sized_with_backend(31, "tmp.ppm", 128, 64, "metal")
expect(backend_req.title).to_equal(widget_showcase_window_title("metal"))
expect(backend_req.window_w).to_equal(128)
```

</details>

#### supports explicit WM child window sizing for scaled frame bridges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = wm_widget_showcase_bridge_request_sized(22, "scaled.ppm", 268, 362)
expect(req.title).to_equal(widget_showcase_window_title("software"))
expect(req.window_w).to_equal(268)
expect(req.window_h).to_equal(362)
expect(req.frame_path).to_equal("scaled.ppm")
```

</details>

#### builds the child environment used by host and simple-os launchers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wm_widget_showcase_client_env("bridge.sdn", "frame.ppm")
expect(env[WM_APP_MODE_ENV]).to_equal(WM_APP_MODE_CLIENT)
expect(env[WM_BRIDGE_FILE_ENV]).to_equal("bridge.sdn")
expect(env[WM_FRAME_FILE_ENV]).to_equal("frame.ppm")
expect(env[WM_EVENT_FILE_ENV]).to_equal("frame.ppm.event")
expect(env[WM_FRAME_SEQ_FILE_ENV]).to_equal("frame.ppm.seq")
expect(env[WM_CLIENT_HOLD_ENV]).to_equal("1")
```

</details>

#### declares child-content pointer input on the shared filesystem bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = wm_fs_app_event(7, "down", 32, 44, 0, true)
val decoded = wm_fs_app_event_decode(wm_fs_app_event_encode(ev))
expect(decoded.seq).to_equal(7)
expect(decoded.kind).to_equal("down")
expect(decoded.x).to_equal(32)
expect(decoded.y).to_equal(44)
expect(decoded.button).to_equal(0)
expect(decoded.pressed).to_equal(true)
```

</details>

#### tracks child frame sequence updates through the bridge request

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = wm_widget_showcase_bridge_request(5, "child.ppm")
expect(req.event_path).to_equal(wm_widget_showcase_event_path("child.ppm"))
expect(req.frame_seq_path).to_equal(wm_widget_showcase_frame_seq_path("child.ppm"))
expect(wm_fs_app_event_seq_path(req.event_path, 3)).to_equal("child.ppm.event.3")
val decoded = wm_fs_bridge_decode(wm_fs_bridge_encode(req))
expect(decoded.event_path).to_equal("child.ppm.event")
expect(decoded.frame_seq_path).to_equal("child.ppm.seq")
```

</details>

#### round-trips a correlated CPU-SIMD frame receipt

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels: [u32] = [0xFF112233u32, 0xFF445566u32, 0xFF778899u32]
val checksum = wm_fs_frame_checksum(pixels)
val receipt = wm_fs_frame_receipt(7, 8, "cpu_simd", "cpu_mirror", 0, 0, pixels.len(), checksum)
val decoded = wm_fs_frame_receipt_decode(wm_fs_frame_receipt_encode(receipt))
expect(wm_fs_frame_receipt_path("child.ppm")).to_equal("child.ppm.receipt")
expect(decoded.event_seq).to_equal(7)
expect(decoded.frame_seq).to_equal(8)
expect(decoded.backend).to_equal("cpu_simd")
expect(decoded.pixel_count).to_equal(3)
expect(decoded.checksum).to_equal(checksum)
expect(wm_fs_frame_receipt_valid(decoded, 7, 8, "cpu_simd", 3)).to_equal(true)
expect(wm_fs_frame_receipt_valid(decoded, 6, 8, "cpu_simd", 3)).to_equal(false)
```

</details>

#### correlates RGB payloads and exact event/frame sequence pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opaque: [u32] = [0xFF112233u32, 0x80445566u32]
val transparent: [u32] = [0x00112233u32, 0x00445566u32]
expect(wm_fs_frame_checksum(opaque)).to_equal(wm_fs_frame_checksum(transparent))
expect(wm_fs_frame_receipt_correlation(2, 8, 3, 8)).to_equal("pending")
expect(wm_fs_frame_receipt_correlation(3, 9, 3, 8)).to_equal("pending")
expect(wm_fs_frame_receipt_correlation(4, 8, 3, 8)).to_equal("invalid")
expect(wm_fs_frame_receipt_correlation(3, 8, 3, 8)).to_equal("ready")
```

</details>

#### requires device readback identity for Vulkan frame receipts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = wm_fs_frame_receipt(4, 5, "vulkan", "device_readback", 91, 92, 2, 123)
val missing_device = wm_fs_frame_receipt(4, 5, "vulkan", "cpu_mirror", 0, 0, 2, 123)
expect(wm_fs_frame_receipt_valid(valid, 4, 5, "vulkan", 2)).to_equal(true)
expect(wm_fs_frame_receipt_valid(missing_device, 4, 5, "vulkan", 2)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_app_process_contract_spec.spl` |
| Updated | 2026-08-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM app process contract.
- WM app process contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
