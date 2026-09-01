# Driver Platform Report Specification

> Tests covering SimpleOS driver platform report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Platform Report Specification

## Scenarios

### SimpleOS driver platform report

#### accepts a complete concrete platform evidence report

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a complete concrete platform evidence report
   - Expected: driver_platform_report_ready(report) is true
   - Expected: driver_platform_report_blocker(report) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a complete concrete platform evidence report")
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

- reports first concrete GPU blocker
   - Expected: driver_platform_report_ready(report) is false
   - Expected: driver_platform_report_blocker(report) equals `gpu:missing-device:intel-anv-level-zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports first concrete GPU blocker")
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

- requires CPU audio acceleration before audio readiness
   - Expected: driver_platform_report_blocker(report) equals `cpu-audio:missing-accel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires CPU audio acceleration before audio readiness")
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

- requires full USB HID input evidence when USB is the input bus
   - Expected: driver_platform_report_blocker(report) equals `input:partial:usb-hid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires full USB HID input evidence when USB is the input bus")
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

- rejects unsafe exokernel raw device grants
   - Expected: driver_platform_report_blocker(report) equals `exokernel:unsafe-raw-device-without-iommu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsafe exokernel raw device grants")
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

- reports team lane blockers after hardware evidence is ready
   - Expected: driver_platform_report_blocker(report) equals `team:missing-tests:audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports team lane blockers after hardware evidence is ready")
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
| Source | `test/unit/os/drivers/driver_platform_report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS driver platform report.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2f8ef2d8ad9d380be3d87cb3bca2352a1d37d8b47d3aba550143c94ffc8b0ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2f8ef2d8ad9d380be3d87cb3bca2352a1d37d8b47d3aba550143c94ffc8b0ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2f8ef2d8ad9d380be3d87cb3bca2352a1d37d8b47d3aba550143c94ffc8b0ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/driver_platform_report_spec.spl
mirror: doc/06_spec/unit/os/drivers/driver_platform_report_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/driver_platform_report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/driver_platform_report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/driver_platform_report_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a complete concrete platform evidence report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/driver_platform_report_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports first concrete GPU blocker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/driver_platform_report_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires CPU audio acceleration before audio readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
