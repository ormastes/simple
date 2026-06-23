# X86 Smf Appscan Qemu Specification

> <details>

<!-- sdn-diagram:id=x86_smf_appscan_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_smf_appscan_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_smf_appscan_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_smf_appscan_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Smf Appscan Qemu Specification

## Scenarios

### x86 SMF appscan QEMU

<details>
<summary>Advanced: launches x64 desktop filesystem apps through the supported disk lane</summary>

#### launches x64 desktop filesystem apps through the supported disk lane _(slow)_

1. print desktop disk missing markers
   - Expected: desktop_disk_serial_accepts_completion(output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run("qemu-system-x86_64"):
    val output = _x64_desktop_disk_output()
    if not desktop_disk_serial_accepts_completion(output):
        print_desktop_disk_missing_markers(output)
    expect(desktop_disk_serial_accepts_completion(output)).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/appscan/x86_smf_appscan_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86 SMF appscan QEMU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
