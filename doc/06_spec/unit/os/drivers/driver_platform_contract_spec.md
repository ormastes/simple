# Driver Platform Contract Specification

> Tests covering SimpleOS driver platform contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Platform Contract Specification

## Scenarios

### SimpleOS driver platform contract

#### accepts baseline and rejects false claims

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts baseline and rejects false claims
   - Expected: driver_platform_accepts(driver_platform_baseline()) is true
   - Expected: driver_platform_false_claim(bad_gpu) is true
   - Expected: driver_platform_false_claim(bad_audio) is true
   - Expected: driver_platform_false_claim(bad_raw) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts baseline and rejects false claims")
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

- selects CPU fallback kernels
   - Expected: cpu_pixel_kernel(x86) equals `x86-avx2`
   - Expected: cpu_audio_kernel(x86) equals `x86-avx2-audio`
   - Expected: cpu_pixel_kernel(mmx) equals `x86-mmx-legacy`
   - Expected: cpu_audio_kernel(mmx) equals `scalar-audio`
   - Expected: cpu_pixel_kernel(arm) equals `arm-sve`
   - Expected: cpu_pixel_kernel(riscv) equals `riscv-rvv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects CPU fallback kernels")
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

- reports GPU vendor probe evidence
   - Expected: gpu_probe_reason(gpu_probe_cuda(true, true, true)) equals `supported`
   - Expected: gpu_probe_reason(gpu_probe_cuda(false, true, true)) equals `missing-runtime:nvidia-cuda`
   - Expected: gpu_probe_reason(gpu_probe_amd(true, true, false, true)) equals `missing-queue:amd-rocm-radv`
   - Expected: gpu_probe_reason(gpu_probe_intel(true, false, false, false)) equals `missing-device:intel-anv-level-zero`
   - Expected: gpu_probe_reason(gpu_probe_qualcomm_arm(true, true, false)) equals `missing-queue:qualcomm-arm-freedreno-turnip-panfrost`
   - Expected: gpu_probe_reason(gpu_probe_riscv(false, true)) equals `missing-runtime:riscv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports GPU vendor probe evidence")
expect(gpu_probe_reason(gpu_probe_cuda(true, true, true))).to_equal("supported")
expect(gpu_probe_reason(gpu_probe_cuda(false, true, true))).to_equal("missing-runtime:nvidia-cuda")
expect(gpu_probe_reason(gpu_probe_amd(true, true, false, true))).to_equal("missing-queue:amd-rocm-radv")
expect(gpu_probe_reason(gpu_probe_intel(true, false, false, false))).to_equal("missing-device:intel-anv-level-zero")
expect(gpu_probe_reason(gpu_probe_qualcomm_arm(true, true, false))).to_equal("missing-queue:qualcomm-arm-freedreno-turnip-panfrost")
expect(gpu_probe_reason(gpu_probe_riscv(false, true))).to_equal("missing-runtime:riscv")
```

</details>

#### reports Intel HDA and Realtek codec probe requirements

- reports Intel HDA and Realtek codec probe requirements
   - Expected: audio_hda_reason(audio_hda_probe(true, true, true, true, "x86-sse2-audio")) equals `supported`
   - Expected: audio_hda_reason(audio_hda_probe(false, true, true, true, "x86-sse2-audio")) equals `missing-controller:intel-hda`
   - Expected: audio_hda_reason(audio_hda_probe(true, false, true, true, "x86-sse2-audio")) equals `missing-codec:realtek-hda`
   - Expected: audio_hda_reason(audio_hda_probe(true, true, false, true, "x86-sse2-audio")) equals `missing-dma-ring:intel-hda`
   - Expected: audio_hda_reason(audio_hda_probe(true, true, true, false, "x86-sse2-audio")) equals `missing-period:intel-hda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Intel HDA and Realtek codec probe requirements")
expect(audio_hda_reason(audio_hda_probe(true, true, true, true, "x86-sse2-audio"))).to_equal("supported")
expect(audio_hda_reason(audio_hda_probe(false, true, true, true, "x86-sse2-audio"))).to_equal("missing-controller:intel-hda")
expect(audio_hda_reason(audio_hda_probe(true, false, true, true, "x86-sse2-audio"))).to_equal("missing-codec:realtek-hda")
expect(audio_hda_reason(audio_hda_probe(true, true, false, true, "x86-sse2-audio"))).to_equal("missing-dma-ring:intel-hda")
expect(audio_hda_reason(audio_hda_probe(true, true, true, false, "x86-sse2-audio"))).to_equal("missing-period:intel-hda")
```

</details>

#### tracks two concrete audio codec brands with CPU acceleration

- tracks two concrete audio codec brands with CPU acceleration
   - Expected: audio_codec_reason(realtek) equals `supported:realtek-hda`
   - Expected: audio_codec_reason(cirrus) equals `supported:cirrus-logic-hda`
   - Expected: audio_codec_reason(slow) equals `missing-cpu-accel:cirrus-logic-hda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks two concrete audio codec brands with CPU acceleration")
val realtek = audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio")
val cirrus = audio_probe_cirrus_logic_hda(true, true, true, true, true, "arm-neon-audio")
val slow = audio_probe_cirrus_logic_hda(true, true, true, true, true, "scalar-audio")
expect(audio_codec_reason(realtek)).to_equal("supported:realtek-hda")
expect(audio_codec_reason(cirrus)).to_equal("supported:cirrus-logic-hda")
expect(audio_codec_reason(slow)).to_equal("missing-cpu-accel:cirrus-logic-hda")
```

</details>

#### reports keyboard and mouse input evidence

- reports keyboard and mouse input evidence
   - Expected: input_probe_reason(input_probe_ps2(true, true, true)) equals `supported:ps2`
   - Expected: input_probe_reason(input_probe_ps2(true, false, true)) equals `missing-mouse:ps2`
   - Expected: input_probe_reason(input_probe_usb_hid(true, true, true, false, true)) equals `partial:usb-hid`
   - Expected: input_probe_reason(input_probe_usb_hid(true, true, true, true, true)) equals `supported:usb-hid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports keyboard and mouse input evidence")
expect(input_probe_reason(input_probe_ps2(true, true, true))).to_equal("supported:ps2")
expect(input_probe_reason(input_probe_ps2(true, false, true))).to_equal("missing-mouse:ps2")
expect(input_probe_reason(input_probe_usb_hid(true, true, true, false, true))).to_equal("partial:usb-hid")
expect(input_probe_reason(input_probe_usb_hid(true, true, true, true, true))).to_equal("supported:usb-hid")
```

</details>

#### requires exokernel grants to protect raw device access

- requires exokernel grants to protect raw device access
   - Expected: exokernel_grant_reason(exokernel_device_grant(true, true, true, true, false, true)) equals `supported`
   - Expected: exokernel_grant_reason(exokernel_device_grant(true, true, true, false, false, false)) equals `missing-iommu-or-broker`
   - Expected: exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, false)) equals `supported`
   - Expected: exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, true)) equals `unsafe-raw-device-without-iommu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires exokernel grants to protect raw device access")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, true, false, true))).to_equal("supported")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, false, false))).to_equal("missing-iommu-or-broker")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, false))).to_equal("supported")
expect(exokernel_grant_reason(exokernel_device_grant(true, true, true, false, true, true))).to_equal("unsafe-raw-device-without-iommu")
```

</details>

#### prepares team lanes with owner, contract, test, doc, and review gates

- prepares team lanes with owner, contract, test, doc, and review gates
   - Expected: driver_team_plan_ready(driver_team_plan(gpu_lane, audio_lane, input_lane, exokernel_lane, mdsoc_lane)) is true
   - Expected: driver_team_plan_blocker(driver_team_plan(gpu_lane, no_audio_tests, input_lane, exokernel_lane, mdsoc_lane)) equals `missing-tests:audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepares team lanes with owner, contract, test, doc, and review gates")
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

- bridges desktop summaries to platform markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges desktop summaries to platform markers")
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
| Source | `test/unit/os/drivers/driver_platform_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS driver platform contract.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd2b92dec1d7c3040574d387dc16684af9ea28d836fa8243656667b02e8c1fdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd2b92dec1d7c3040574d387dc16684af9ea28d836fa8243656667b02e8c1fdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd2b92dec1d7c3040574d387dc16684af9ea28d836fa8243656667b02e8c1fdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/driver_platform_contract_spec.spl
mirror: doc/06_spec/unit/os/drivers/driver_platform_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/driver_platform_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/driver_platform_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/driver_platform_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts baseline and rejects false claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/driver_platform_contract_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects CPU fallback kernels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/driver_platform_contract_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports GPU vendor probe evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
