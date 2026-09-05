# Driver Platform Report Specification

> 1. gpu probe intel

<!-- sdn-diagram:id=driver_platform_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_platform_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_platform_report_spec -> std
driver_platform_report_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_platform_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Platform Report Specification

## Scenarios

### SimpleOS driver platform report

#### accepts a complete concrete platform evidence report

1. gpu probe intel
2. cpu accel features
3. audio probe realtek hda
4. audio probe cirrus logic hda
5. input probe ps2
6. exokernel device grant
7. ready team plan
   - Expected: driver_platform_report_ready(report) is true
   - Expected: driver_platform_report_blocker(report) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = driver_platform_report(
    gpu_probe_intel(true, true, true, true),
    cpu_accel_features("x86_64", true, true, true, true, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "x86-sse2-audio"),
    input_probe_ps2(true, true, true),
    exokernel_device_grant(true, true, true, true, false, true),
    ready_team_plan()
)
expect(driver_platform_report_ready(report)).to_equal(true)
expect(driver_platform_report_blocker(report)).to_equal("ready")
expect(driver_platform_report_marker(report)).to_contain("[driver-platform-report] status=ready")
```

</details>

#### reports first concrete GPU blocker

1. gpu probe intel
2. cpu accel features
3. audio probe realtek hda
4. audio probe cirrus logic hda
5. input probe ps2
6. exokernel device grant
7. ready team plan
   - Expected: driver_platform_report_ready(report) is false
   - Expected: driver_platform_report_blocker(report) equals `gpu:missing-device:intel-anv-level-zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = driver_platform_report(
    gpu_probe_intel(true, false, true, true),
    cpu_accel_features("x86_64", true, true, true, true, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "x86-sse2-audio"),
    input_probe_ps2(true, true, true),
    exokernel_device_grant(true, true, true, true, false, true),
    ready_team_plan()
)
expect(driver_platform_report_ready(report)).to_equal(false)
expect(driver_platform_report_blocker(report)).to_equal("gpu:missing-device:intel-anv-level-zero")
```

</details>

#### requires CPU audio acceleration before audio readiness

1. gpu probe intel
2. cpu accel features
3. audio probe realtek hda
4. audio probe cirrus logic hda
5. input probe ps2
6. exokernel device grant
7. ready team plan
   - Expected: driver_platform_report_blocker(report) equals `cpu-audio:missing-accel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = driver_platform_report(
    gpu_probe_intel(true, true, true, true),
    cpu_accel_features("x86", true, false, false, false, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "scalar-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "scalar-audio"),
    input_probe_ps2(true, true, true),
    exokernel_device_grant(true, true, true, true, false, true),
    ready_team_plan()
)
expect(driver_platform_report_blocker(report)).to_equal("cpu-audio:missing-accel")
```

</details>

#### requires full USB HID input evidence when USB is the input bus

1. gpu probe intel
2. cpu accel features
3. audio probe realtek hda
4. audio probe cirrus logic hda
5. input probe usb hid
6. exokernel device grant
7. ready team plan
   - Expected: driver_platform_report_blocker(report) equals `input:partial:usb-hid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = driver_platform_report(
    gpu_probe_intel(true, true, true, true),
    cpu_accel_features("x86_64", true, true, true, true, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "x86-sse2-audio"),
    input_probe_usb_hid(true, true, true, false, true),
    exokernel_device_grant(true, true, true, true, false, true),
    ready_team_plan()
)
expect(driver_platform_report_blocker(report)).to_equal("input:partial:usb-hid")
```

</details>

#### rejects unsafe exokernel raw device grants

1. gpu probe intel
2. cpu accel features
3. audio probe realtek hda
4. audio probe cirrus logic hda
5. input probe ps2
6. exokernel device grant
7. ready team plan
   - Expected: driver_platform_report_blocker(report) equals `exokernel:unsafe-raw-device-without-iommu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = driver_platform_report(
    gpu_probe_intel(true, true, true, true),
    cpu_accel_features("x86_64", true, true, true, true, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "x86-sse2-audio"),
    input_probe_ps2(true, true, true),
    exokernel_device_grant(true, true, true, false, true, true),
    ready_team_plan()
)
expect(driver_platform_report_blocker(report)).to_equal("exokernel:unsafe-raw-device-without-iommu")
```

</details>

#### reports team lane blockers after hardware evidence is ready

1. driver team lane
2. driver team lane
3. driver team lane
4. driver team lane
5. driver team lane
6. gpu probe intel
7. cpu accel features
8. audio probe realtek hda
9. audio probe cirrus logic hda
10. input probe ps2
11. exokernel device grant
   - Expected: driver_platform_report_blocker(report) equals `team:missing-tests:audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val team = driver_team_plan(
    driver_team_lane("gpu", "driver-gpu", true, true, true, true),
    driver_team_lane("audio", "driver-audio", true, false, true, true),
    driver_team_lane("input", "driver-input", true, true, true, true),
    driver_team_lane("exokernel", "driver-exokernel", true, true, true, true),
    driver_team_lane("mdsoc", "driver-architect", true, true, true, true)
)
val report = driver_platform_report(
    gpu_probe_intel(true, true, true, true),
    cpu_accel_features("x86_64", true, true, true, true, false, false, false),
    audio_probe_realtek_hda(true, true, true, true, true, "x86-sse2-audio"),
    audio_probe_cirrus_logic_hda(true, true, true, true, true, "x86-sse2-audio"),
    input_probe_ps2(true, true, true),
    exokernel_device_grant(true, true, true, true, false, true),
    team
)
expect(driver_platform_report_blocker(report)).to_equal("team:missing-tests:audio")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/driver_platform_report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS driver platform report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
