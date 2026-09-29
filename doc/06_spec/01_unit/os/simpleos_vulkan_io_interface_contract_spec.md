# simpleos_vulkan_io_interface_contract_spec

> Purpose: should select Vulkan and expose the canonical DrawIR executor

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_vulkan_io_interface_contract_spec

Purpose: should select Vulkan and expose the canonical DrawIR executor

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should select Vulkan and expose the canonical DrawIR executor
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### SimpleOS Vulkan and VirtIO device interfaces

#### should select Vulkan and expose the canonical DrawIR executor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should select Vulkan and expose the canonical DrawIR executor
- Verify: should select Vulkan and expose the canonical DrawIR executor


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should select Vulkan and expose the canonical DrawIR executor")
step("Verify: should select Vulkan and expose the canonical DrawIR executor")
# @req: REQ-OS-SimpVulkIoInteCont-001
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

- should reject Vulkan output without device readback provenance
- Verify: should reject Vulkan output without device readback provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject Vulkan output without device readback provenance")
step("Verify: should reject Vulkan output without device readback provenance")
# @req: REQ-OS-SimpVulkIoInteCont-001
val engine = engine_source()
val daemon = daemon_source()
expect(engine).to_contain("rb.source != \"host_cache_after_device_copy\"")
expect(engine).to_contain("if rb.backend_handle <= 0 and rb.device_identity <= 0:")
expect(daemon).to_contain("result.readback_source == \"device_readback\"")
expect(daemon).to_contain("result.backend_handle > 0")
expect(daemon).to_contain("result.readback_checksum > 0")
expect(daemon).to_contain("device_identity > 0")
```

</details>

#### should require complete DrawIR commands and pixel coverage

- should require complete DrawIR commands and pixel coverage
- Verify: should require complete DrawIR commands and pixel coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should require complete DrawIR commands and pixel coverage")
step("Verify: should require complete DrawIR commands and pixel coverage")
# @req: REQ-OS-SimpVulkIoInteCont-001
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

- should expose ARM VirtIO keyboard and pointer records through one poll seam
- Verify: should expose ARM VirtIO keyboard and pointer records through one poll seam


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should expose ARM VirtIO keyboard and pointer records through one poll seam")
step("Verify: should expose ARM VirtIO keyboard and pointer records through one poll seam")
# @req: REQ-OS-SimpVulkIoInteCont-001
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

- should preserve both sides of Ctrl and Alt through VirtIO input
- Verify: should preserve both sides of Ctrl and Alt through VirtIO input
   - Expected: key_to_canon(evdev_key_to_key(KEY_LEFTCTRL)) equals `key_to_canon(Key.LeftCtrl)`
   - Expected: key_to_canon(evdev_key_to_key(KEY_RIGHTCTRL)) equals `key_to_canon(Key.RightCtrl)`
   - Expected: key_to_canon(evdev_key_to_key(KEY_LEFTALT)) equals `key_to_canon(Key.LeftAlt)`
   - Expected: key_to_canon(evdev_key_to_key(KEY_RIGHTALT)) equals `key_to_canon(Key.RightAlt)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should preserve both sides of Ctrl and Alt through VirtIO input")
step("Verify: should preserve both sides of Ctrl and Alt through VirtIO input")
# @req: REQ-OS-SimpVulkIoInteCont-001
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

- should validate bounded VirtIO audio and capture completion
- Verify: should validate bounded VirtIO audio and capture completion
   - Expected: negotiation.status equals `accepted`
   - Expected: valid.status equals `accepted`
   - Expected: valid.period_bytes equals `1024`
   - Expected: valid.buffer_bytes equals `4096`
   - Expected: completion.status equals `completed`
   - Expected: completion.kind equals `capture-period`
   - Expected: stale.status equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should validate bounded VirtIO audio and capture completion")
step("Verify: should validate bounded VirtIO audio and capture completion")
# @req: REQ-OS-SimpVulkIoInteCont-001
val audio = audio_source()
val negotiation = virtio_snd_negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1)
expect(negotiation.status).to_equal("accepted")
expect(negotiation.playback).to_be(true)
expect(negotiation.capture).to_be(true)
val request = VirtioSndPcmRequest(stream_id: 1, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 256, periods: 4, buffer_frames: 1024)
val valid = virtio_snd_validate_pcm(request)
expect(valid.status).to_equal("accepted")
expect(valid.period_bytes).to_equal(1024)  # oracle: value fixed by the spec contract
expect(valid.buffer_bytes).to_equal(4096)  # oracle: value fixed by the spec contract
val completion = virtio_snd_completion(7u64, 1, 3u64, 3u64, 256, "capture")
expect(completion.status).to_equal("completed")
expect(completion.kind).to_equal("capture-period")
val stale = virtio_snd_completion(7u64, 1, 3u64, 4u64, 256, "capture")
expect(stale.status).to_equal("stale-generation")
expect(audio).to_contain("me configure_capture(stream_id: u32, period_frames: i64, channels: i64, spin_limit: i64)")
expect(audio).to_contain("me submit_capture() -> VirtioSndServiceReceipt:")
expect(audio).to_contain("me poll_capture() -> VirtioSndServiceReceipt:")
expect(audio).to_contain("me poll_capture_receipt() -> VirtioSndCaptureReceipt:")
expect(audio).to_contain("capture_session: u64")
expect(audio).to_contain("capture_generation: u64")
expect(audio).to_contain("sample_hash = (sample_hash * 65599 + sample + 32768) % 2147483647")
expect(audio).to_contain("virtio_snd_dma_sync_for_cpu(self.dma)")
```

</details>

#### should fail closed on audio geometry, shutdown, and generation loss

- should fail closed on audio geometry, shutdown, and generation loss
- Verify: should fail closed on audio geometry, shutdown, and generation loss
   - Expected: malformed.status equals `invalid-buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should fail closed on audio geometry, shutdown, and generation loss")
step("Verify: should fail closed on audio geometry, shutdown, and generation loss")
# @req: REQ-OS-SimpVulkIoInteCont-001
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

#### should distinguish QEMU readiness from live guest Vulkan and IO evidence

- should distinguish QEMU readiness from live guest Vulkan and IO evidence
- Verify: should distinguish QEMU readiness from live guest Vulkan and IO evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should distinguish QEMU readiness from live guest Vulkan and IO evidence")
step("Verify: should distinguish QEMU readiness from live guest Vulkan and IO evidence")
# @req: REQ-OS-SimpVulkIoInteCont-001
val qemu = qemu_gpu_checker_source()
val audio = qemu_audio_checker_source()
expect(qemu).to_contain("qemu-system-x86_64")
expect(qemu).to_contain("qemu-system-aarch64")
expect(qemu).to_contain("qemu-system-riscv64")
expect(qemu).to_contain("qemu_accel_for_isa")
expect(qemu).to_contain("virtio-(gpu|vga)")
expect(qemu).to_contain("ivshmem-plain")
expect(qemu).to_contain("qemu-host-offload-transport-available")
expect(qemu).to_contain("qemu-host-offload-transport-missing")
expect(qemu).to_contain("guest-artifact-missing")
expect(qemu).to_contain("pure-simple-compiler-missing")
expect(qemu).to_contain("HOST_GPU_FIXTURE_OK")
expect(qemu).to_contain("render_backend=vulkan")
expect(qemu).to_contain("render_readback_p95_us=")
expect(qemu).to_contain("identity=")
expect(qemu).to_contain("HOST_GPU_RENDER_OK")
expect(audio).to_contain("virtio-sound-(device|pci)")
expect(audio).to_contain("virtio-input-host-(device|pci)")
expect(audio).to_contain("simpleos_io_audio_qemu_preflight=pass")
expect(audio).to_contain("guest_execution=1")
expect(audio).to_contain("seed_rejected=1")
```

</details>

#### should validate reusable host and guest profiles without promoting readiness to PASS

- should validate reusable host and guest profiles without promoting readiness to PASS
- Verify: should validate reusable host and guest profiles without promoting readiness to PASS
   - Expected: profiles.len() equals `3`
   - Expected: ready.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: ready.reason equals `live-guest-proof-required`
   - Expected: macos.required_evidence equals `UiEnvironmentEvidenceClass.HostReadiness`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should validate reusable host and guest profiles without promoting readiness to PASS")
step("Verify: should validate reusable host and guest profiles without promoting readiness to PASS")
# @req: REQ-OS-SimpVulkIoInteCont-001
val profiles = simpleos_qemu_2d_environment_profiles()
expect(profiles.len()).to_equal(3)  # oracle: value fixed by the spec contract
for profile in profiles:
    expect(ui_environment_profile_valid(profile)).to_be(true)
    val ready = validate_ui_environment_evidence(
        profile,
        ui_environment_evidence(
            profile.id,
            UiEnvironmentEvidenceClass.HostReadiness,
            configured: true,
            runtime_available: true,
            qemu_arguments_bound: true
        )
    )
    expect(ready.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
    expect(ready.reason).to_equal("live-guest-proof-required")
    expect(ready.promotion_eligible).to_be(false)
val macos = macos_emulated_2d_environment_profile()
expect(ui_environment_profile_valid(macos)).to_be(true)
expect(macos.required_evidence).to_equal(UiEnvironmentEvidenceClass.HostReadiness)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-OS-SimpVulkIoInteCont-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2265e9379a54824ed8e9546e997bd0dec378691e6fd3a0116382b0531c8c7ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2265e9379a54824ed8e9546e997bd0dec378691e6fd3a0116382b0531c8c7ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2265e9379a54824ed8e9546e997bd0dec378691e6fd3a0116382b0531c8c7ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl
mirror: doc/06_spec/01_unit/os/simpleos_vulkan_io_interface_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/simpleos_vulkan_io_interface_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/simpleos_vulkan_io_interface_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should select Vulkan and expose the canonical DrawIR executor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should select Vulkan and expose the canonical DrawIR executor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject Vulkan output without device readback provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject Vulkan output without device readback provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require complete DrawIR commands and pixel coverage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require complete DrawIR commands and pixel coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose ARM VirtIO keyboard and pointer records through one poll seam' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve both sides of Ctrl and Alt through VirtIO input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/simpleos_vulkan_io_interface_contract_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate bounded VirtIO audio and capture completion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
