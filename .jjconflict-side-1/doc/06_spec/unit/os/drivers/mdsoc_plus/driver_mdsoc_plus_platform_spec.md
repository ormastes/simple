# Driver Mdsoc Plus Platform Specification

> Tests covering SimpleOS Driver MDSOC+ Platform, GPU lane, Audio lane, Input lane, Exokernel lane, MDSOC lane.

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

- vendor_list contains all five vendors
   - Expected: lst contains `nvidia-cuda`
   - Expected: lst contains `riscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vendor_list contains all five vendors")
val lst = gpu_lane_vendor_list()
expect(lst.contains("nvidia-cuda")).to_equal(true)
expect(lst.contains("riscv")).to_equal(true)
```

</details>

#### supports all five vendors

- supports all five vendors
   - Expected: gpu_lane_supports_vendor("nvidia-cuda") is true
   - Expected: gpu_lane_supports_vendor("amd-rocm-radv") is true
   - Expected: gpu_lane_supports_vendor("intel-anv-level-zero") is true
   - Expected: gpu_lane_supports_vendor("qualcomm-arm-freedreno-turnip-panfrost") is true
   - Expected: gpu_lane_supports_vendor("riscv") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports all five vendors")
expect(gpu_lane_supports_vendor("nvidia-cuda")).to_equal(true)
expect(gpu_lane_supports_vendor("amd-rocm-radv")).to_equal(true)
expect(gpu_lane_supports_vendor("intel-anv-level-zero")).to_equal(true)
expect(gpu_lane_supports_vendor("qualcomm-arm-freedreno-turnip-panfrost")).to_equal(true)
expect(gpu_lane_supports_vendor("riscv")).to_equal(true)
```

</details>

#### rejects unknown vendor

- rejects unknown vendor
   - Expected: gpu_lane_supports_vendor("unknown-gpu") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown vendor")
expect(gpu_lane_supports_vendor("unknown-gpu")).to_equal(false)
```

</details>

#### compute allowed only for cuda amd intel

- compute allowed only for cuda amd intel
   - Expected: gpu_lane_compute_allowed("nvidia-cuda") is true
   - Expected: gpu_lane_compute_allowed("amd-rocm-radv") is true
   - Expected: gpu_lane_compute_allowed("intel-anv-level-zero") is true
   - Expected: gpu_lane_compute_allowed("riscv") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute allowed only for cuda amd intel")
expect(gpu_lane_compute_allowed("nvidia-cuda")).to_equal(true)
expect(gpu_lane_compute_allowed("amd-rocm-radv")).to_equal(true)
expect(gpu_lane_compute_allowed("intel-anv-level-zero")).to_equal(true)
expect(gpu_lane_compute_allowed("riscv")).to_equal(false)
```

</details>

#### riscv is software vulkan vendor

- riscv is software vulkan vendor
   - Expected: gpu_lane_software_vulkan_vendor("riscv") is true
   - Expected: gpu_lane_software_vulkan_vendor("nvidia-cuda") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv is software vulkan vendor")
expect(gpu_lane_software_vulkan_vendor("riscv")).to_equal(true)
expect(gpu_lane_software_vulkan_vendor("nvidia-cuda")).to_equal(false)
```

</details>

#### probe label ready when all caps present

- probe label ready when all caps present
   - Expected: lbl equals `gpu-lane:ready:nvidia-cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label ready when all caps present")
val lbl = gpu_lane_probe_label("nvidia-cuda", true, true, true, true)
expect(lbl).to_equal("gpu-lane:ready:nvidia-cuda")
```

</details>

#### probe label missing-runtime when runtime false

- probe label missing-runtime when runtime false
   - Expected: lbl equals `gpu-lane:missing-runtime:amd-rocm-radv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label missing-runtime when runtime false")
val lbl = gpu_lane_probe_label("amd-rocm-radv", false, true, true, true)
expect(lbl).to_equal("gpu-lane:missing-runtime:amd-rocm-radv")
```

</details>

#### framebuffer compute is forbidden

- framebuffer compute is forbidden
   - Expected: gpu_lane_framebuffer_compute_forbidden() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("framebuffer compute is forbidden")
expect(gpu_lane_framebuffer_compute_forbidden()).to_equal(true)
```

</details>

### Audio lane

#### controller is intel-hda

- controller is intel-hda
   - Expected: audio_lane_controller() equals `intel-hda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("controller is intel-hda")
expect(audio_lane_controller()).to_equal("intel-hda")
```

</details>

#### primary codec is realtek-hda

- primary codec is realtek-hda
   - Expected: audio_lane_primary_codec() equals `realtek-hda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("primary codec is realtek-hda")
expect(audio_lane_primary_codec()).to_equal("realtek-hda")
```

</details>

#### secondary codec is cirrus-logic-hda

- secondary codec is cirrus-logic-hda
   - Expected: audio_lane_secondary_codec() equals `cirrus-logic-hda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("secondary codec is cirrus-logic-hda")
expect(audio_lane_secondary_codec()).to_equal("cirrus-logic-hda")
```

</details>

#### codec_supported accepts realtek and cirrus

- codec_supported accepts realtek and cirrus
   - Expected: audio_lane_codec_supported("realtek-hda") is true
   - Expected: audio_lane_codec_supported("cirrus-logic-hda") is true
   - Expected: audio_lane_codec_supported("other-codec") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("codec_supported accepts realtek and cirrus")
expect(audio_lane_codec_supported("realtek-hda")).to_equal(true)
expect(audio_lane_codec_supported("cirrus-logic-hda")).to_equal(true)
expect(audio_lane_codec_supported("other-codec")).to_equal(false)
```

</details>

#### probe label ready when all present

- probe label ready when all present
   - Expected: lbl equals `audio-lane:ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label ready when all present")
val lbl = audio_lane_probe_label(true, true, true, true, "alsa")
expect(lbl).to_equal("audio-lane:ready")
```

</details>

#### probe label missing-controller when controller false

- probe label missing-controller when controller false
   - Expected: lbl equals `audio-lane:missing-controller`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label missing-controller when controller false")
val lbl = audio_lane_probe_label(false, true, true, true, "alsa")
expect(lbl).to_equal("audio-lane:missing-controller")
```

</details>

#### dma without period is invalid

- dma without period is invalid
   - Expected: audio_lane_dma_without_period_invalid(true, false) is true
   - Expected: audio_lane_dma_without_period_invalid(true, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dma without period is invalid")
expect(audio_lane_dma_without_period_invalid(true, false)).to_equal(true)
expect(audio_lane_dma_without_period_invalid(true, true)).to_equal(false)
```

</details>

### Input lane

#### ps2 bus name correct

- ps2 bus name correct
   - Expected: input_lane_ps2_bus() equals `ps2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ps2 bus name correct")
expect(input_lane_ps2_bus()).to_equal("ps2")
```

</details>

#### usb hid bus name correct

- usb hid bus name correct
   - Expected: input_lane_usb_hid_bus() equals `usb-hid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("usb hid bus name correct")
expect(input_lane_usb_hid_bus()).to_equal("usb-hid")
```

</details>

#### ps2 hotplug not supported usb hotplug supported

- ps2 hotplug not supported usb hotplug supported
   - Expected: input_lane_ps2_hotplug_supported() is false
   - Expected: input_lane_usb_hid_hotplug_supported() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ps2 hotplug not supported usb hotplug supported")
expect(input_lane_ps2_hotplug_supported()).to_equal(false)
expect(input_lane_usb_hid_hotplug_supported()).to_equal(true)
```

</details>

#### probe label ready for ps2 with all caps

- probe label ready for ps2 with all caps
   - Expected: lbl equals `input-lane:ready:ps2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label ready for ps2 with all caps")
val lbl = input_lane_probe_label("ps2", true, true, true)
expect(lbl).to_equal("input-lane:ready:ps2")
```

</details>

#### probe label missing-keyboard when keyboard false

- probe label missing-keyboard when keyboard false
   - Expected: lbl equals `input-lane:missing-keyboard:ps2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label missing-keyboard when keyboard false")
val lbl = input_lane_probe_label("ps2", false, true, true)
expect(lbl).to_equal("input-lane:missing-keyboard:ps2")
```

</details>

#### usb partial without hotplug detected

- usb partial without hotplug detected
   - Expected: input_lane_usb_partial_without_hotplug("usb-hid", false, true) is true
   - Expected: input_lane_usb_partial_without_hotplug("usb-hid", true, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("usb partial without hotplug detected")
expect(input_lane_usb_partial_without_hotplug("usb-hid", false, true)).to_equal(true)
expect(input_lane_usb_partial_without_hotplug("usb-hid", true, true)).to_equal(false)
```

</details>

### Exokernel lane

#### resource list contains bar irq dma

- resource list contains bar irq dma
   - Expected: res contains `bar`
   - Expected: res contains `irq`
   - Expected: res contains `dma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resource list contains bar irq dma")
val res = exokernel_lane_resources()
expect(res.contains("bar")).to_equal(true)
expect(res.contains("irq")).to_equal(true)
expect(res.contains("dma")).to_equal(true)
```

</details>

#### raw app without iommu is unsafe

- raw app without iommu is unsafe
   - Expected: exokernel_lane_raw_app_requires_iommu(true, false) is true
   - Expected: exokernel_lane_raw_app_requires_iommu(true, true) is false
   - Expected: exokernel_lane_raw_app_requires_iommu(false, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw app without iommu is unsafe")
expect(exokernel_lane_raw_app_requires_iommu(true, false)).to_equal(true)
expect(exokernel_lane_raw_app_requires_iommu(true, true)).to_equal(false)
expect(exokernel_lane_raw_app_requires_iommu(false, false)).to_equal(false)
```

</details>

#### probe label ready when all caps present

- probe label ready when all caps present
   - Expected: lbl equals `exokernel-lane:ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label ready when all caps present")
val lbl = exokernel_lane_probe_label(true, true, true, true, true, false)
expect(lbl).to_equal("exokernel-lane:ready")
```

</details>

#### probe label unsafe when raw without iommu

- probe label unsafe when raw without iommu
   - Expected: lbl equals `exokernel-lane:unsafe-raw-without-iommu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label unsafe when raw without iommu")
val lbl = exokernel_lane_probe_label(true, true, true, false, true, true)
expect(lbl).to_equal("exokernel-lane:unsafe-raw-without-iommu")
```

</details>

#### probe label missing-bar when bar false

- probe label missing-bar when bar false
   - Expected: lbl equals `exokernel-lane:missing-bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe label missing-bar when bar false")
val lbl = exokernel_lane_probe_label(false, true, true, true, true, false)
expect(lbl).to_equal("exokernel-lane:missing-bar")
```

</details>

#### brokered iommu is safe

- brokered iommu is safe
   - Expected: exokernel_lane_brokered_iommu_safe() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("brokered iommu is safe")
expect(exokernel_lane_brokered_iommu_safe()).to_equal(true)
```

</details>

### MDSOC lane

#### required layers contains all four

- required layers contains all four
   - Expected: res contains `os-kernel`
   - Expected: res contains `driver-supervisor`
   - Expected: res contains `pcimgr`
   - Expected: res contains `ipc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("required layers contains all four")
val res = mdsoc_lane_required_layers()
expect(res.contains("os-kernel")).to_equal(true)
expect(res.contains("driver-supervisor")).to_equal(true)
expect(res.contains("pcimgr")).to_equal(true)
expect(res.contains("ipc")).to_equal(true)
```

</details>

#### visibility allowed from driver-supervisor to os-kernel

- visibility allowed from driver-supervisor to os-kernel
   - Expected: mdsoc_lane_visibility_allowed("driver-supervisor", "os-kernel") is true
   - Expected: mdsoc_lane_visibility_allowed("pcimgr", "driver-supervisor") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visibility allowed from driver-supervisor to os-kernel")
expect(mdsoc_lane_visibility_allowed("driver-supervisor", "os-kernel")).to_equal(true)
expect(mdsoc_lane_visibility_allowed("pcimgr", "driver-supervisor")).to_equal(true)
```

</details>

#### visibility forbidden from os-kernel to driver-supervisor

- visibility forbidden from os-kernel to driver-supervisor
   - Expected: mdsoc_lane_visibility_forbidden("os-kernel", "driver-supervisor") is true
   - Expected: mdsoc_lane_visibility_forbidden("pcimgr", "ipc") is true
   - Expected: mdsoc_lane_visibility_forbidden("driver-supervisor", "os-kernel") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visibility forbidden from os-kernel to driver-supervisor")
expect(mdsoc_lane_visibility_forbidden("os-kernel", "driver-supervisor")).to_equal(true)
expect(mdsoc_lane_visibility_forbidden("pcimgr", "ipc")).to_equal(true)
expect(mdsoc_lane_visibility_forbidden("driver-supervisor", "os-kernel")).to_equal(false)
```

</details>

#### release gate label ready when all present

- release gate label ready when all present
   - Expected: lbl equals `mdsoc-lane:ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("release gate label ready when all present")
val lbl = mdsoc_lane_release_gate_label(true, true, true, true, true)
expect(lbl).to_equal("mdsoc-lane:ready")
```

</details>

#### release gate label missing-owner when owner false

- release gate label missing-owner when owner false
   - Expected: lbl equals `mdsoc-lane:missing-owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("release gate label missing-owner when owner false")
val lbl = mdsoc_lane_release_gate_label(false, true, true, true, true)
expect(lbl).to_equal("mdsoc-lane:missing-owner")
```

</details>

#### plan complete when all lanes ready

- plan complete when all lanes ready
   - Expected: mdsoc_lane_plan_complete(true, true, true, true, true) is true
   - Expected: mdsoc_lane_plan_complete(true, true, true, true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan complete when all lanes ready")
expect(mdsoc_lane_plan_complete(true, true, true, true, true)).to_equal(true)
expect(mdsoc_lane_plan_complete(true, true, true, true, false)).to_equal(false)
```

</details>

#### plan blocker identifies first failing lane

- plan blocker identifies first failing lane
   - Expected: blk equals `blocking-lane:mdsoc`
   - Expected: blk2 equals `blocking-lane:gpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan blocker identifies first failing lane")
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
| Source | `test/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Driver MDSOC+ Platform, GPU lane, Audio lane, Input lane, Exokernel lane, MDSOC lane.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8746fab7337496f06ec5a8c4880fac2d82034c9bd58eee894a904da3f6787afc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8746fab7337496f06ec5a8c4880fac2d82034c9bd58eee894a904da3f6787afc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8746fab7337496f06ec5a8c4880fac2d82034c9bd58eee894a904da3f6787afc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl
mirror: doc/06_spec/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vendor_list contains all five vendors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports all five vendors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/mdsoc_plus/driver_mdsoc_plus_platform_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown vendor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
