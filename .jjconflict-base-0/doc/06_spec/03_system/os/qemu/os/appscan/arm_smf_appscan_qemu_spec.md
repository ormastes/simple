# Arm Smf Appscan Qemu Specification

> <details>

<!-- sdn-diagram:id=arm_smf_appscan_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm_smf_appscan_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm_smf_appscan_qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm_smf_appscan_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm Smf Appscan Qemu Specification

## Scenarios

### ARM SMF appscan QEMU

<details>
<summary>Advanced: discovers and launches ARM32 SMF apps through the supported filesystem lane</summary>

#### discovers and launches ARM32 SMF apps through the supported filesystem lane _(slow)_

1.  assert arm common smf appscan
2.  assert arm32 trace appscan


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run("qemu-system-arm"):
    val output = _arm32_output()
    _assert_arm_common_smf_appscan(output)
    _assert_arm32_trace_appscan(output)
```

</details>


</details>

<details>
<summary>Advanced: discovers and launches ARM64 SMF apps through the supported filesystem lane</summary>

#### discovers and launches ARM64 SMF apps through the supported filesystem lane _(slow)_

1.  assert arm common smf appscan
2.  assert arm64 process appscan


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run("qemu-system-aarch64"):
    val output = _arm64_output()
    _assert_arm_common_smf_appscan(output)
    _assert_arm64_process_appscan(output)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/appscan/arm_smf_appscan_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM SMF appscan QEMU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
