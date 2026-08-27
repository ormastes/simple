# Driver Mdsoc Plus Platform Specification

> <details>

<!-- sdn-diagram:id=driver_mdsoc_plus_platform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_mdsoc_plus_platform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_mdsoc_plus_platform_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_mdsoc_plus_platform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Mdsoc Plus Platform Specification

## Scenarios

### SimpleOS Driver MDSOC+ Platform

### GPU lane

#### vendor_list contains all five vendors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lst = gpu_lane_vendor_list()
expect(lst.contains("nvidia-cuda")).to_equal(true)
expect(lst.contains("riscv")).to_equal(true)
```

</details>

#### supports all five vendors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_lane_supports_vendor("nvidia-cuda")).to_equal(true)
expect(gpu_lane_supports_vendor("amd-rocm-radv")).to_equal(true)
expect(gpu_lane_supports_vendor("intel-anv-level-zero")).to_equal(true)
expect(gpu_lane_supports_vendor("qualcomm-arm-freedreno-turnip-panfrost")).to_equal(true)
expect(gpu_lane_supports_vendor("riscv")).to_equal(true)
```

</details>

#### rejects unknown vendor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_lane_supports_vendor("unknown-gpu")).to_equal(false)
```

</details>

#### compute allowed only for cuda amd intel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_lane_compute_allowed("nvidia-cuda")).to_equal(true)
expect(gpu_lane_compute_allowed("amd-rocm-radv")).to_equal(true)
expect(gpu_lane_compute_allowed("intel-anv-level-zero")).to_equal(true)
expect(gpu_lane_compute_allowed("riscv")).to_equal(false)
```

</details>

#### riscv is software vulkan vendor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_lane_software_vulkan_vendor("riscv")).to_equal(true)
expect(gpu_lane_software_vulkan_vendor("nvidia-cuda")).to_equal(false)
```

</details>

#### probe label ready when all caps present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = gpu_lane_probe_label("nvidia-cuda", true, true, true, true)
expect(lbl).to_equal("gpu-lane:ready:nvidia-cuda")
```

</details>

#### probe label missing-runtime when runtime false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = gpu_lane_probe_label("amd-rocm-radv", false, true, true, true)
expect(lbl).to_equal("gpu-lane:missing-runtime:amd-rocm-radv")
```

</details>

#### framebuffer compute is forbidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_lane_framebuffer_compute_forbidden()).to_equal(true)
```

</details>

### Audio lane

#### controller is intel-hda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_lane_controller()).to_equal("intel-hda")
```

</details>

#### primary codec is realtek-hda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_lane_primary_codec()).to_equal("realtek-hda")
```

</details>

#### secondary codec is cirrus-logic-hda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_lane_secondary_codec()).to_equal("cirrus-logic-hda")
```

</details>

#### codec_supported accepts realtek and cirrus

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_lane_codec_supported("realtek-hda")).to_equal(true)
expect(audio_lane_codec_supported("cirrus-logic-hda")).to_equal(true)
expect(audio_lane_codec_supported("other-codec")).to_equal(false)
```

</details>

#### probe label ready when all present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = audio_lane_probe_label(true, true, true, true, "alsa")
expect(lbl).to_equal("audio-lane:ready")
```

</details>

#### probe label missing-controller when controller false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = audio_lane_probe_label(false, true, true, true, "alsa")
expect(lbl).to_equal("audio-lane:missing-controller")
```

</details>

#### dma without period is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_lane_dma_without_period_invalid(true, false)).to_equal(true)
expect(audio_lane_dma_without_period_invalid(true, true)).to_equal(false)
```

</details>

### Input lane

#### ps2 bus name correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(input_lane_ps2_bus()).to_equal("ps2")
```

</details>

#### usb hid bus name correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(input_lane_usb_hid_bus()).to_equal("usb-hid")
```

</details>

#### ps2 hotplug not supported usb hotplug supported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(input_lane_ps2_hotplug_supported()).to_equal(false)
expect(input_lane_usb_hid_hotplug_supported()).to_equal(true)
```

</details>

#### probe label ready for ps2 with all caps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = input_lane_probe_label("ps2", true, true, true)
expect(lbl).to_equal("input-lane:ready:ps2")
```

</details>

#### probe label missing-keyboard when keyboard false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = input_lane_probe_label("ps2", false, true, true)
expect(lbl).to_equal("input-lane:missing-keyboard:ps2")
```

</details>

#### usb partial without hotplug detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(input_lane_usb_partial_without_hotplug("usb-hid", false, true)).to_equal(true)
expect(input_lane_usb_partial_without_hotplug("usb-hid", true, true)).to_equal(false)
```

</details>

### Exokernel lane

#### resource list contains bar irq dma

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = exokernel_lane_resources()
expect(res.contains("bar")).to_equal(true)
expect(res.contains("irq")).to_equal(true)
expect(res.contains("dma")).to_equal(true)
```

</details>

#### raw app without iommu is unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exokernel_lane_raw_app_requires_iommu(true, false)).to_equal(true)
expect(exokernel_lane_raw_app_requires_iommu(true, true)).to_equal(false)
expect(exokernel_lane_raw_app_requires_iommu(false, false)).to_equal(false)
```

</details>

#### probe label ready when all caps present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = exokernel_lane_probe_label(true, true, true, true, true, false)
expect(lbl).to_equal("exokernel-lane:ready")
```

</details>

#### probe label unsafe when raw without iommu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = exokernel_lane_probe_label(true, true, true, false, true, true)
expect(lbl).to_equal("exokernel-lane:unsafe-raw-without-iommu")
```

</details>

#### probe label missing-bar when bar false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = exokernel_lane_probe_label(false, true, true, true, true, false)
expect(lbl).to_equal("exokernel-lane:missing-bar")
```

</details>

#### brokered iommu is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exokernel_lane_brokered_iommu_safe()).to_equal(true)
```

</details>

### MDSOC lane

#### required layers contains all four

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = mdsoc_lane_required_layers()
expect(res.contains("os-kernel")).to_equal(true)
expect(res.contains("driver-supervisor")).to_equal(true)
expect(res.contains("pcimgr")).to_equal(true)
expect(res.contains("ipc")).to_equal(true)
```

</details>

#### visibility allowed from driver-supervisor to os-kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mdsoc_lane_visibility_allowed("driver-supervisor", "os-kernel")).to_equal(true)
expect(mdsoc_lane_visibility_allowed("pcimgr", "driver-supervisor")).to_equal(true)
```

</details>

#### visibility forbidden from os-kernel to driver-supervisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mdsoc_lane_visibility_forbidden("os-kernel", "driver-supervisor")).to_equal(true)
expect(mdsoc_lane_visibility_forbidden("pcimgr", "ipc")).to_equal(true)
expect(mdsoc_lane_visibility_forbidden("driver-supervisor", "os-kernel")).to_equal(false)
```

</details>

#### release gate label ready when all present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = mdsoc_lane_release_gate_label(true, true, true, true, true)
expect(lbl).to_equal("mdsoc-lane:ready")
```

</details>

#### release gate label missing-owner when owner false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = mdsoc_lane_release_gate_label(false, true, true, true, true)
expect(lbl).to_equal("mdsoc-lane:missing-owner")
```

</details>

#### plan complete when all lanes ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mdsoc_lane_plan_complete(true, true, true, true, true)).to_equal(true)
expect(mdsoc_lane_plan_complete(true, true, true, true, false)).to_equal(false)
```

</details>

#### plan blocker identifies first failing lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blk = mdsoc_lane_plan_blocker(true, true, true, true, false)
expect(blk).to_equal("blocking-lane:mdsoc")
val blk2 = mdsoc_lane_plan_blocker(false, true, true, true, true)
expect(blk2).to_equal("blocking-lane:gpu")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Driver MDSOC+ Platform
- GPU lane
- Audio lane
- Input lane
- Exokernel lane
- MDSOC lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
