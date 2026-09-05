# Environment Profile Specification

> Tests covering Reusable UI environment profiles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Environment Profile Specification

## Scenarios

### Reusable UI environment profiles

#### selects canonical host and SimpleOS QEMU profiles from one catalog

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects canonical host and SimpleOS QEMU profiles from one catalog
   - Expected: all.len() equals `5`
   - Expected: qemu.len() equals `3`
   - Expected: qemu[0].id equals `simpleos-qemu-x86_64-vulkan-virtio`
   - Expected: qemu[1].id equals `simpleos-qemu-aarch64-vulkan-virtio`
   - Expected: qemu[2].id equals `simpleos-qemu-riscv64-vulkan-virtio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selects canonical host and SimpleOS QEMU profiles from one catalog")
val all = ui_2d_environment_profiles()
val qemu = simpleos_qemu_2d_environment_profiles()
expect(all.len()).to_equal(5)
expect(qemu.len()).to_equal(3)
for profile in all:
    expect(ui_environment_profile_valid(profile)).to_be(true)
expect(qemu[0].id).to_equal("simpleos-qemu-x86_64-vulkan-virtio")
expect(qemu[1].id).to_equal("simpleos-qemu-aarch64-vulkan-virtio")
expect(qemu[2].id).to_equal("simpleos-qemu-riscv64-vulkan-virtio")
match ui_environment_profile_by_id(qemu[1].id):
    case Some(selected): expect(selected.id).to_equal(qemu[1].id)
    case None: fail("canonical profile was not selectable by id")
expect(ui_environment_profile_by_id("unknown-profile")).to_be_nil()
```

</details>

#### keeps configured host readiness distinct from live execution

- keeps configured host readiness distinct from live execution
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `live-host-proof-required`
   - Expected: ui_environment_admission_status_name(admission.status) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps configured host readiness distinct from live execution")
val linux = linux_host_2d_environment_profile()
val admission = validate_ui_environment_evidence(linux, readiness(linux))
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
expect(admission.reason).to_equal("live-host-proof-required")
expect(admission.promotion_eligible).to_be(false)
expect(ui_environment_admission_status_name(admission.status)).to_equal("ready")
```

</details>

#### keeps configured QEMU readiness distinct from live guest proof

- keeps configured QEMU readiness distinct from live guest proof
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `live-guest-proof-required`
   - Expected: ui_environment_evidence_class_name(profile.required_evidence) equals `live-guest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps configured QEMU readiness distinct from live guest proof")
val profile = simpleos_qemu_2d_environment_profiles()[0]
val admission = validate_ui_environment_evidence(profile, readiness(profile))
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
expect(admission.reason).to_equal("live-guest-proof-required")
expect(admission.promotion_eligible).to_be(false)
expect(ui_environment_evidence_class_name(profile.required_evidence)).to_equal("live-guest")
```

</details>

#### admits the canonical ARM64 QEMU primitive configuration only as ready

- admits the canonical ARM64 QEMU primitive configuration only as ready
   - Expected: config.machine equals `virt`
   - Expected: config.pci_transport equals `pcie`
   - Expected: config.mmio_transport equals `virtio-mmio`
   - Expected: config.ivshmem_device equals `ivshmem-plain,memdev=hostgpu`
   - Expected: config.keyboard_device equals `virtio-keyboard-device`
   - Expected: config.pointer_device equals `virtio-mouse-device`
   - Expected: config.sound_device equals `virtio-sound-device`
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `arm64-qemu-primitives-ready-live-guest-proof-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits the canonical ARM64 QEMU primitive configuration only as ready")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val config = arm64_simpleos_qemu_primitive_config()
val admission = arm64_primitive_readiness(profile, config)
expect(arm64_simpleos_qemu_primitive_config_valid(config)).to_be(true)
expect(config.machine).to_equal("virt")
expect(config.pci_transport).to_equal("pcie")
expect(config.mmio_transport).to_equal("virtio-mmio")
expect(config.ivshmem_device).to_equal("ivshmem-plain,memdev=hostgpu")
expect(config.keyboard_device).to_equal("virtio-keyboard-device")
expect(config.pointer_device).to_equal("virtio-mouse-device")
expect(config.sound_device).to_equal("virtio-sound-device")
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
expect(admission.reason).to_equal("arm64-qemu-primitives-ready-live-guest-proof-required")
expect(admission.promotion_eligible).to_be(false)
```

</details>

#### keeps ARM64 configuration facts aligned with the canonical wrappers

- keeps ARM64 configuration facts aligned with the canonical wrappers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps ARM64 configuration facts aligned with the canonical wrappers")
val host_gpu = rt_file_read_text(
    "scripts/check/check-simpleos-qemu-host-gpu-2d.shs") ?? ""
val input = rt_file_read_text(
    "scripts/check/check-simpleos-arm64-qmp-input-evidence.shs") ?? ""
val audio = rt_file_read_text(
    "scripts/check/check-simpleos-virtio-snd-qemu.shs") ?? ""
expect(host_gpu).to_contain("-machine virt")
expect(host_gpu).to_contain("-device virtio-net-pci")
expect(host_gpu).to_contain("-device ivshmem-plain,memdev=hostgpu")
expect(input).to_contain("-device virtio-keyboard-device")
expect(input).to_contain("-device virtio-mouse-device")
expect(audio).to_contain("-device virtio-sound-device,audiodev=audio0")
```

</details>

#### blocks missing ARM64 machine PCI MMIO and shared-memory bindings

- blocks missing ARM64 machine PCI MMIO and shared-memory bindings
   - Expected: machine.status equals `UiEnvironmentAdmissionStatus.Blocked`
   - Expected: machine.reason equals `arm64-qemu-machine-unbound`
   - Expected: pci.reason equals `arm64-qemu-pci-unbound`
   - Expected: mmio.reason equals `arm64-qemu-mmio-unbound`
   - Expected: ivshmem.reason equals `arm64-qemu-ivshmem-unbound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks missing ARM64 machine PCI MMIO and shared-memory bindings")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val machine = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(machine: "q35")
)
val pci = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(pci_transport: "")
)
val mmio = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(mmio_transport: "pci-only")
)
val ivshmem = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(
        ivshmem_device: "ivshmem-plain,memdev=other"
    )
)
expect(machine.status).to_equal(UiEnvironmentAdmissionStatus.Blocked)
expect(machine.reason).to_equal("arm64-qemu-machine-unbound")
expect(pci.reason).to_equal("arm64-qemu-pci-unbound")
expect(mmio.reason).to_equal("arm64-qemu-mmio-unbound")
expect(ivshmem.reason).to_equal("arm64-qemu-ivshmem-unbound")
```

</details>

#### blocks missing ARM64 VirtIO input and sound devices

- blocks missing ARM64 VirtIO input and sound devices
   - Expected: keyboard.reason equals `arm64-qemu-keyboard-unbound`
   - Expected: pointer.reason equals `arm64-qemu-pointer-unbound`
   - Expected: sound.reason equals `arm64-qemu-sound-unbound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks missing ARM64 VirtIO input and sound devices")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val keyboard = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(keyboard_device: "")
)
val pointer = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(pointer_device: "")
)
val sound = arm64_primitive_readiness(
    profile,
    arm64_simpleos_qemu_primitive_config(sound_device: "")
)
expect(keyboard.reason).to_equal("arm64-qemu-keyboard-unbound")
expect(pointer.reason).to_equal("arm64-qemu-pointer-unbound")
expect(sound.reason).to_equal("arm64-qemu-sound-unbound")
```

</details>

#### rejects incomplete or fallback ARM64 live guest primitive evidence

- rejects incomplete or fallback ARM64 live guest primitive evidence
   - Expected: no_boot.reason equals `guest-boot-proof-missing`
   - Expected: no_driver.reason equals `guest-driver-ready-proof-missing`
   - Expected: no_draw_ir.reason equals `draw-ir-execution-proof-missing`
   - Expected: no_physical_device.reason equals `vulkan-physical-device-proof-missing`
   - Expected: no_device_execution.reason equals `vulkan-device-execution-proof-missing`
   - Expected: no_readback.reason equals `device-readback-proof-missing`
   - Expected: fallback.reason equals `fallback-used`
   - Expected: no_keyboard_queue.reason equals `keyboard-queue-proof-missing`
   - Expected: no_pointer_queue.reason equals `pointer-queue-proof-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 120 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects incomplete or fallback ARM64 live guest primitive evidence")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val config = arm64_simpleos_qemu_primitive_config()
val no_boot = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest
    )
)
val no_driver = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true
    )
)
val no_draw_ir = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true
    )
)
val no_physical_device = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true
    )
)
val no_device_execution = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0"
    )
)
val no_readback = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true
    )
)
val fallback = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true,
        device_readback: true,
        fallback_used: true
    )
)
val no_keyboard_queue = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true,
        device_readback: true
    )
)
val no_pointer_queue = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true,
        device_readback: true,
        keyboard_queue_ready: true
    )
)
expect(no_boot.reason).to_equal("guest-boot-proof-missing")
expect(no_driver.reason).to_equal("guest-driver-ready-proof-missing")
expect(no_draw_ir.reason).to_equal("draw-ir-execution-proof-missing")
expect(no_physical_device.reason).to_equal("vulkan-physical-device-proof-missing")
expect(no_device_execution.reason).to_equal("vulkan-device-execution-proof-missing")
expect(no_readback.reason).to_equal("device-readback-proof-missing")
expect(fallback.reason).to_equal("fallback-used")
expect(no_keyboard_queue.reason).to_equal("keyboard-queue-proof-missing")
expect(no_pointer_queue.reason).to_equal("pointer-queue-proof-missing")
```

</details>

#### rejects missing ARM64 guest audio queue and completion evidence

- rejects missing ARM64 guest audio queue and completion evidence
   - Expected: no_audio_queue.reason equals `audio-queue-proof-missing`
   - Expected: no_audio_completion.reason equals `audio-completion-proof-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing ARM64 guest audio queue and completion evidence")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val config = arm64_simpleos_qemu_primitive_config()
val no_audio_queue = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id, UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true, guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true, device_readback: true,
        keyboard_queue_ready: true, pointer_queue_ready: true
    )
)
val no_audio_completion = validate_arm64_simpleos_qemu_primitives(
    profile,
    config,
    arm64_simpleos_qemu_primitive_evidence(
        profile.id, UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true, guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true, device_readback: true,
        keyboard_queue_ready: true, pointer_queue_ready: true,
        audio_queue_ready: true
    )
)
expect(no_audio_queue.reason).to_equal("audio-queue-proof-missing")
expect(no_audio_completion.reason).to_equal("audio-completion-proof-missing")
```

</details>

#### passes complete ARM64 guest boot driver Vulkan readback input and audio evidence

- passes complete ARM64 guest boot driver Vulkan readback input and audio evidence
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Pass`
   - Expected: admission.reason equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes complete ARM64 guest boot driver Vulkan readback input and audio evidence")
val profile = simpleos_qemu_2d_environment_profiles()[1]
val admission = validate_arm64_simpleos_qemu_primitives(
    profile,
    arm64_simpleos_qemu_primitive_config(),
    arm64_simpleos_qemu_primitive_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.LiveGuest,
        guest_booted: true,
        guest_driver_ready: true,
        draw_ir_executed: true,
        vulkan_physical_device: "hostgpu-physical-0",
        vulkan_device_executed: true,
        device_readback: true,
        keyboard_queue_ready: true,
        pointer_queue_ready: true,
        audio_queue_ready: true,
        audio_completed: true
    )
)
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Pass)
expect(admission.reason).to_equal("pass")
expect(admission.promotion_eligible).to_be(true)
```

</details>

#### keeps the postponed macOS profile readiness-only

- keeps the postponed macOS profile readiness-only
   - Expected: profile.execution equals `UiEnvironmentExecution.EmulatedContract`
   - Expected: profile.input equals `UiEnvironmentInput.EmulatedEvents`
   - Expected: profile.audio equals `UiEnvironmentAudio.EmulatedAudio`
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `readiness-only-profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the postponed macOS profile readiness-only")
val profile = macos_emulated_2d_environment_profile()
expect(profile.execution).to_equal(UiEnvironmentExecution.EmulatedContract)
expect(profile.input).to_equal(UiEnvironmentInput.EmulatedEvents)
expect(profile.audio).to_equal(UiEnvironmentAudio.EmulatedAudio)
val admission = validate_ui_environment_evidence(profile, readiness(profile))
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
expect(admission.reason).to_equal("readiness-only-profile")
expect(admission.promotion_eligible).to_be(false)
```

</details>

#### admits complete correlated live host and guest evidence

- admits complete correlated live host and guest evidence
   - Expected: host_admission.status equals `UiEnvironmentAdmissionStatus.Pass`
   - Expected: guest_admission.status equals `UiEnvironmentAdmissionStatus.Pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits complete correlated live host and guest evidence")
val host = linux_host_2d_environment_profile()
val guest = simpleos_qemu_2d_environment_profiles()[1]
val host_admission = validate_ui_environment_evidence(
    host,
    complete_live(host, UiEnvironmentEvidenceClass.LiveHost)
)
val guest_admission = validate_ui_environment_evidence(
    guest,
    complete_live(guest, UiEnvironmentEvidenceClass.LiveGuest)
)
expect(host_admission.status).to_equal(UiEnvironmentAdmissionStatus.Pass)
expect(host_admission.promotion_eligible).to_be(true)
expect(guest_admission.status).to_equal(UiEnvironmentAdmissionStatus.Pass)
expect(guest_admission.promotion_eligible).to_be(true)
```

</details>

#### fails claimed live guest evidence without boot and device proof

- fails claimed live guest evidence without boot and device proof
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Fail`
   - Expected: admission.reason equals `guest-boot-proof-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails claimed live guest evidence without boot and device proof")
val profile = simpleos_qemu_2d_environment_profiles()[2]
val no_boot = ui_environment_evidence(
    profile.id,
    UiEnvironmentEvidenceClass.LiveGuest,
    configured: true,
    runtime_available: true,
    qemu_arguments_bound: true
)
val admission = validate_ui_environment_evidence(profile, no_boot)
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Fail)
expect(admission.reason).to_equal("guest-boot-proof-missing")
expect(admission.promotion_eligible).to_be(false)
```

</details>

#### fails live proof that used fallback

- fails live proof that used fallback
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Fail`
   - Expected: admission.reason equals `fallback-used`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails live proof that used fallback")
val profile = simpleos_qemu_2d_environment_profiles()[0]
val evidence = ui_environment_evidence(
    profile.id,
    UiEnvironmentEvidenceClass.LiveGuest,
    configured: true,
    runtime_available: true,
    qemu_arguments_bound: true,
    guest_booted: true,
    draw_ir_executed: true,
    vulkan_device_executed: true,
    device_readback: true,
    input_delivered: true,
    audio_completed: true,
    fallback_used: true,
    device_identity: "device-41",
    frame_identity: "frame-7"
)
val admission = validate_ui_environment_evidence(profile, evidence)
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Fail)
expect(admission.reason).to_equal("fallback-used")
```

</details>

#### blocks incomplete configuration before interpreting execution fields

- blocks incomplete configuration before interpreting execution fields
   - Expected: validate_ui_environment_evidence(profile, missing_config).reason equals `environment-not-configured`
   - Expected: validate_ui_environment_evidence(profile, missing_runtime).reason equals `runtime-unavailable`
   - Expected: validate_ui_environment_evidence(profile, missing_qemu_args).reason equals `qemu-arguments-unbound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks incomplete configuration before interpreting execution fields")
val profile = simpleos_qemu_2d_environment_profiles()[0]
val missing_config = ui_environment_evidence(
    profile.id,
    UiEnvironmentEvidenceClass.HostReadiness
)
val missing_runtime = ui_environment_evidence(
    profile.id,
    UiEnvironmentEvidenceClass.HostReadiness,
    configured: true
)
val missing_qemu_args = ui_environment_evidence(
    profile.id,
    UiEnvironmentEvidenceClass.HostReadiness,
    configured: true,
    runtime_available: true
)
expect(validate_ui_environment_evidence(profile, missing_config).reason).to_equal("environment-not-configured")
expect(validate_ui_environment_evidence(profile, missing_runtime).reason).to_equal("runtime-unavailable")
expect(validate_ui_environment_evidence(profile, missing_qemu_args).reason).to_equal("qemu-arguments-unbound")
```

</details>

#### rejects evidence bound to a different profile

- rejects evidence bound to a different profile
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Fail`
   - Expected: admission.reason equals `profile-identity-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects evidence bound to a different profile")
val profile = simpleos_qemu_2d_environment_profiles()[0]
val evidence = ui_environment_evidence(
    "simpleos-qemu-aarch64-vulkan-virtio",
    UiEnvironmentEvidenceClass.HostReadiness,
    configured: true,
    runtime_available: true,
    qemu_arguments_bound: true
)
val admission = validate_ui_environment_evidence(profile, evidence)
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Fail)
expect(admission.reason).to_equal("profile-identity-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/environment_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Reusable UI environment profiles.
- Reusable UI environment profiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-003`
- `REQ-008`
- `REQ-011`
- `REQ-019`
- `REQ-020`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4bcf71bfb10c273940d211b1d7346d32d2e3adee68e05b295827f12f343c0c73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4bcf71bfb10c273940d211b1d7346d32d2e3adee68e05b295827f12f343c0c73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4bcf71bfb10c273940d211b1d7346d32d2e3adee68e05b295827f12f343c0c73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/spec/environment_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/environment_profile_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/spec/environment_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/environment_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/environment_profile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/environment_profile_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/spec/environment_profile_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects canonical host and SimpleOS QEMU profiles from one catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/environment_profile_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the canonical ARM64 QEMU primitive configuration only as ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/environment_profile_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ARM64 configuration facts aligned with the canonical wrappers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
