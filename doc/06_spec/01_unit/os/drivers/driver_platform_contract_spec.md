# Driver Platform Contract Specification

> <details>

<!-- sdn-diagram:id=driver_platform_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_platform_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_platform_contract_spec -> std
driver_platform_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_platform_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Platform Contract Specification

## Scenarios

### SimpleOS driver platform contract

#### accepts baseline and rejects false claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_gpu = driver_platform_summary("virtio-gpu", true, "intel-hda", "realtek-hda", true, true, "ps2", true, "ps2", true, "bar,irq,dma,iommu:brokered", "brokered", false)
val bad_audio = driver_platform_summary("virtio-gpu", false, "intel-hda", "realtek-hda", true, false, "ps2", true, "ps2", true, "bar,irq,dma,iommu:brokered", "brokered", false)
val bad_raw = driver_platform_summary("virtio-gpu", false, "intel-hda", "realtek-hda", true, true, "ps2", true, "ps2", true, "bar,irq,dma", "none", true)
expect(driver_platform_accepts(driver_platform_baseline())).to_equal(true)
expect(driver_platform_false_claim(bad_gpu)).to_equal(true)
expect(driver_platform_false_claim(bad_audio)).to_equal(true)
expect(driver_platform_false_claim(bad_raw)).to_equal(true)
expect(driver_platform_marker(driver_platform_baseline())).to_contain("[driver-platform] gpu=virtio-gpu")
```

</details>

#### selects CPU fallback kernels

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = cpu_accel_features("x86_64", true, true, true, true, false, false, false)
val mmx = cpu_accel_features("x86", true, false, false, false, false, false, false)
val arm = cpu_accel_features("arm64", false, false, false, false, true, true, false)
val riscv = cpu_accel_features("riscv64", false, false, false, false, false, false, true)
expect(cpu_pixel_kernel(x86)).to_equal("x86-avx2")
expect(cpu_audio_kernel(x86)).to_equal("x86-avx2-audio")
expect(cpu_pixel_kernel(mmx)).to_equal("x86-mmx-legacy")
expect(cpu_audio_kernel(mmx)).to_equal("scalar-audio")
expect(cpu_pixel_kernel(arm)).to_equal("arm-sve")
expect(cpu_pixel_kernel(riscv)).to_equal("riscv-rvv")
```

</details>

#### reports GPU vendor probe evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_probe_reason(gpu_probe_cuda(true, true, true))).to_equal("supported")
expect(gpu_probe_reason(gpu_probe_cuda(false, true, true))).to_equal("missing-runtime:nvidia-cuda")
expect(gpu_probe_reason(gpu_probe_amd(true, true, false, true))).to_equal("missing-queue:amd-rocm-radv")
expect(gpu_probe_reason(gpu_probe_intel(true, false, false, false))).to_equal("missing-device:intel-anv-level-zero")
expect(gpu_probe_reason(gpu_probe_qualcomm_arm(true, true, false))).to_equal("missing-queue:qualcomm-arm-freedreno-turnip-panfrost")
expect(gpu_probe_reason(gpu_probe_riscv(false, true))).to_equal("missing-runtime:riscv")
```

</details>

#### reports Intel HDA and Realtek codec probe requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(audio_hda_reason(audio_hda_probe(true, true, true, true, "x86-sse2-audio"))).to_equal("supported")
expect(audio_hda_reason(audio_hda_probe(false, true, true, true, "x86-sse2-audio"))).to_equal("missing-controller:intel-hda")
expect(audio_hda_reason(audio_hda_probe(true, false, true, true, "x86-sse2-audio"))).to_equal("missing-codec:realtek-hda")
expect(audio_hda_reason(audio_hda_probe(true, true, false, true, "x86-sse2-audio"))).to_equal("missing-dma-ring:intel-hda")
expect(audio_hda_reason(audio_hda_probe(true, true, true, false, "x86-sse2-audio"))).to_equal("missing-period:intel-hda")
```

</details>

#### tracks two concrete audio codec brands with CPU acceleration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val realtek = audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio")
val cirrus = audio_probe_cirrus_logic_hda(true, true, true, true, true, "arm-neon-audio")
val slow = audio_probe_cirrus_logic_hda(true, true, true, true, true, "scalar-audio")
expect(audio_codec_reason(realtek)).to_equal("supported:realtek-hda")
expect(audio_codec_reason(cirrus)).to_equal("supported:cirrus-logic-hda")
expect(audio_codec_reason(slow)).to_equal("missing-cpu-accel:cirrus-logic-hda")
```

</details>

#### reports keyboard and mouse input evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(input_probe_reason(input_probe_ps2(true, true, true))).to_equal("supported:ps2")
expect(input_probe_reason(input_probe_ps2(true, false, true))).to_equal("missing-mouse:ps2")
expect(input_probe_reason(input_probe_usb_hid(true, true, true, false, true))).to_equal("partial:usb-hid")
expect(input_probe_reason(input_probe_usb_hid(true, true, true, true, true))).to_equal("supported:usb-hid")
```

</details>

#### requires exokernel grants to protect raw device access

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, true, false, true))).to_equal("supported")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, false, false))).to_equal("missing-iommu-or-broker")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, false))).to_equal("supported")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, true))).to_equal("unsafe-raw-device-without-iommu")
```

</details>

#### prepares team lanes with owner, contract, test, doc, and review gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpu_lane = driver_team_lane("gpu", "driver-gpu", true, true, true, true)
val audio_lane = driver_team_lane("audio", "driver-audio", true, true, true, true)
val input_lane = driver_team_lane("input", "driver-input", true, true, true, true)
val exokernel_lane = driver_team_lane("exokernel", "driver-exokernel", true, true, true, true)
val mdsoc_lane = driver_team_lane("mdsoc", "driver-architect", true, true, true, true)
val no_audio_tests = driver_team_lane("audio", "driver-audio", true, false, true, true)
expect(driver_team_plan_ready(driver_team_plan(gpu_lane, audio_lane, input_lane, exokernel_lane, mdsoc_lane))).to_equal(true)
expect(driver_team_plan_blocker(driver_team_plan(gpu_lane, no_audio_tests, input_lane, exokernel_lane, mdsoc_lane))).to_equal("missing-tests:audio")
```

</details>

#### bridges desktop summaries to platform markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "virtio-gpu", "virtio-gpu", true, "virtio-net")
val marker = desktop_driver_platform_marker(summary)
expect(marker).to_contain("[driver-platform] gpu=virtio-gpu")
expect(marker).to_contain("audio=intel-hda")
expect(marker).to_contain("audio_codec=realtek-hda")
expect(marker).to_contain("keyboard=ps2")
expect(marker).to_contain("mouse=ps2")
expect(marker).to_contain("exokernel=bar,irq,dma,iommu:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/driver_platform_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS driver platform contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
