# Usb Installer Layout Specification

> <details>

<!-- sdn-diagram:id=usb_installer_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=usb_installer_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

usb_installer_layout_spec -> std
usb_installer_layout_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=usb_installer_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Usb Installer Layout Specification

## Scenarios

### USB installer layout helpers

#### detects at least the QEMU virtio target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disks = detect_disks()
expect(disks.len()).to_be_greater_than(0)
expect(disks[0].path).to_equal("/dev/vda")
```

</details>

#### uses an EFI plus root plus swap default plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disks = detect_disks()
val plan = default_partition_plan(disks[0])
expect(plan.efi_size_mb).to_equal(256)
expect(plan.root_size_mb).to_equal(0)
expect(plan.swap_size_mb).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/usb_installer_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- USB installer layout helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
