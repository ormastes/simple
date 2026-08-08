# Simpleos Vulkan Io Interface Contract Specification

> Tests covering SimpleOS Vulkan and VirtIO device interfaces.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Vulkan Io Interface Contract Specification

## Scenarios

### SimpleOS Vulkan and VirtIO device interfaces

#### should select Vulkan and expose the canonical DrawIR executor

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = engine_source()
val draw_ir = draw_ir_source()
expect(engine).to_contain("static fn create_vulkan_backend(width: i32, height: i32)")
expect(engine).to_contain("selected_backend_name: \"vulkan\"")
expect(engine).to_contain("if self.selected_backend_name == \"vulkan\":")
expect(draw_ir).to_contain("engine2d_draw_ir_adv_fresh_device_composition_with_images")
expect(draw_ir).to_contain("selected_backend: text")
expect(draw_ir).to_contain("readback_source: text")
```

</details>

#### should reject Vulkan output without device readback provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = engine_source()
val daemon = daemon_source()
expect(engine).to_contain("if rb.source != \"device_readback\" and rb.source != \"host_cache_after_device_present\":")
expect(engine).to_contain("if rb.backend_handle <= 0 and rb.device_identity <= 0:")
expect(daemon).to_contain("result.readback_source == \"device_readback\"")
expect(daemon).to_contain("result.backend_handle > 0")
expect(daemon).to_contain("result.readback_checksum > 0")
expect(daemon).to_contain("device_identity > 0")
```

</details>

#### should require complete DrawIR commands and pixel coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daemon = daemon_source()
val draw_ir = draw_ir_source()
expect(daemon).to_contain("result.skipped_command_count == 0")
expect(daemon).to_contain("result.rendered_command_count.to_i64() == element_count")
expect(daemon).to_contain("result.pixels.len().to_i64() >= output_count")
expect(daemon).to_contain("SIMPLEOS_HOST_GPU_REASON_NON_DEVICE_READBACK")
expect(draw_ir).to_contain("fallback_required: bool")
```

</details>

#### should expose ARM VirtIO keyboard and pointer records through one poll seam

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = input_source()
val backend = input_backend_source()
expect(input).to_contain("fn arm64_virtio_input_init() -> u32:")
expect(input).to_contain("fn arm64_virtio_input_poll() -> VirtioInputEvent?:")
expect(input).to_contain("device_kind: rt_arm64_virtio_input_event_device_kind()")
expect(input).to_contain("irq_status: rt_arm64_virtio_input_event_irq_status()")
expect(backend).to_contain("impl InputBackend for Arm64VirtioInputBackend:")
expect(backend).to_contain("VIRTIO_INPUT_DEVICE_KEYBOARD")
expect(backend).to_contain("VIRTIO_INPUT_DEVICE_POINTER")
expect(backend).to_contain("self.pending_mouse = self.mouse.feed_syn()")
```

</details>

#### should preserve both sides of Ctrl and Alt through VirtIO input

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = input_backend_source()
expect(key_to_canon(evdev_key_to_key(KEY_LEFTCTRL))).to_equal(key_to_canon(Key.LeftCtrl))
expect(key_to_canon(evdev_key_to_key(KEY_RIGHTCTRL))).to_equal(key_to_canon(Key.RightCtrl))
expect(key_to_canon(evdev_key_to_key(KEY_LEFTALT))).to_equal(key_to_canon(Key.LeftAlt))
expect(key_to_canon(evdev_key_to_key(KEY_RIGHTALT))).to_equal(key_to_canon(Key.RightAlt))
expect(backend).to_contain("self.left_alt = pressed")
expect(backend).to_contain("self.right_alt = pressed")
expect(backend).to_contain("self.left_ctrl = pressed")
expect(backend).to_contain("self.right_ctrl = pressed")
expect(backend).to_contain("self.ctrl_held()")
expect(backend).to_contain("self.alt_held()")
```

</details>

#### should validate bounded VirtIO audio and capture completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val audio = audio_source()
val negotiation = virtio_snd_negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1)
expect(negotiation.status).to_equal("accepted")
expect(negotiation.playback).to_be(true)
expect(negotiation.capture).to_be(true)
val request = VirtioSndPcmRequest(stream_id: 1, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 256, periods: 4, buffer_frames: 1024)
val valid = virtio_snd_validate_pcm(request)
expect(valid.status).to_equal("accepted")
expect(valid.period_bytes).to_equal(1024)
expect(valid.buffer_bytes).to_equal(4096)
val completion = virtio_snd_completion(7u64, 1, 3u64, 3u64, 256, "capture")
expect(completion.status).to_equal("completed")
expect(completion.kind).to_equal("capture-period")
val stale = virtio_snd_completion(7u64, 1, 3u64, 4u64, 256, "capture")
expect(stale.status).to_equal("stale-generation")
expect(audio).to_contain("me configure_capture(stream_id: u32, period_frames: i64, channels: i64, spin_limit: i64)")
expect(audio).to_contain("me submit_capture() -> VirtioSndServiceReceipt:")
expect(audio).to_contain("me poll_capture() -> VirtioSndServiceReceipt:")
expect(audio).to_contain("virtio_snd_dma_sync_for_cpu(self.dma)")
```

</details>

#### should fail closed on audio geometry, shutdown, and generation loss

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val audio = audio_source()
val protocol = file_read_text("src/os/drivers/virtio/virtio_snd_protocol.spl")
expect(audio).to_contain("if not self.ready or self.direction != \"capture\" or self.period_frames <= 0:")
expect(audio).to_contain("if not self.ready or self.direction != \"playback\" or self.period_frames <= 0")
expect(audio).to_contain("virtio_snd_dma_destroy(self.dma)")
expect(audio).to_contain("self.ready = false")
expect(protocol).to_contain("if completion_generation != expected_generation:")
expect(protocol).to_contain("kind = if direction == \"capture\": \"capture-period\"")
val malformed = virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 1, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 8, periods: 1, buffer_frames: 8))
expect(malformed.status).to_equal("invalid-buffer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl` |
| Updated | 2026-08-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Vulkan and VirtIO device interfaces.
- SimpleOS Vulkan and VirtIO device interfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
