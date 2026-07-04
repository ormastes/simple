# X86 64 Desktop Driver Completion Specification

> <details>

<!-- sdn-diagram:id=x86_64_desktop_driver_completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_desktop_driver_completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_desktop_driver_completion_spec -> std
x86_64_desktop_driver_completion_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_desktop_driver_completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Desktop Driver Completion Specification

## Scenarios

### x86_64 desktop driver completion marker contract

#### accepts only the complete QEMU desktop driver summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = complete_driver_summary()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(true)
```

</details>

#### rejects resident process fallback as incomplete

1. complete lane evidence
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complete = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "bga", "framebuffer", false, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" +
    complete_lane_evidence() +
    "[desktop-e2e] process-backed:resident app=browser_demo pid=10737\n"
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects false VGA acceleration claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complete = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "vga", "vga", true, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" + complete_lane_evidence()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects zero PCI enumeration even with later evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complete = desktop_driver_summary_for_uefi_qemu(true, 0, "nvme", "virtio-gpu", "virtio-gpu", true, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" + complete_lane_evidence()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects absent storage display dma interrupt input or network evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_storage = desktop_driver_summary_for_uefi_qemu(true, 5, "none", "virtio-gpu", "virtio-gpu", true, "virtio-net")
val no_display = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "none", "none", false, "virtio-net")
val no_network = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "virtio-gpu", "virtio-gpu", true, "unsupported")
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_storage) + "\n" + complete_lane_evidence())).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_display) + "\n" + complete_lane_evidence())).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_network) + "\n" + complete_lane_evidence())).to_equal(false)
```

</details>

#### requires all process-backed desktop app markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = complete_driver_summary().replace(
    "[desktop-e2e] process-backed:ok app=file_manager pid=15\n",
    ""
)
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### requires generic VFS app-read and virtio-net queue smoke evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_vfs = complete_driver_summary().replace(
    "[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/browser_demo bytes=4096\n",
    ""
)
val missing_info_vfs = complete_driver_summary().replace(
    "[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/info bytes=4096\n",
    ""
)
val missing_rx = complete_driver_summary().replace(
    "[desktop-e2e] virtio-net:rx-queue=ok queue=0\n",
    ""
)
val missing_bounded_smoke = complete_driver_summary().replace(
    "[desktop-e2e] network-smoke:bounded ok packets=2 timeout_ms=500\n",
    ""
)
expect(desktop_driver_summary_accepts_complete_qemu(missing_vfs)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_info_vfs)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_rx)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_bounded_smoke)).to_equal(false)
```

</details>

#### wires the runner UEFI serial acceptance to the completion contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = complete_driver_summary()
expect(desktop_uefi_serial_accepts_completion(summary)).to_equal(true)
expect(desktop_uefi_serial_accepts_completion(summary.replace(
    "[desktop-e2e] virtio-net:tx-queue=ok queue=0\n",
    ""
))).to_equal(false)
expect(desktop_uefi_required_marker_fragments()).to_contain("[desktop-e2e] network-smoke:bounded ok packets=")
```

</details>

#### rejects hidden copy and resident VFS fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hidden_copy = complete_driver_summary() + "[desktop-e2e] dma:hidden-copy fallback=true\n"
val resident_vfs = complete_driver_summary() + "[desktop-e2e] vfs-app-read:resident path=/sys/apps/browser_demo\n"
expect(desktop_driver_summary_accepts_complete_qemu(hidden_copy)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(resident_vfs)).to_equal(false)
```

</details>

#### does not treat the current direct QEMU lane as UEFI-complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = desktop_driver_summary_for_qemu_direct(true)
val summary = desktop_driver_summary_text(direct) + "\n" + complete_lane_evidence()
expect(summary.contains("boot=qemu-direct")).to_equal(true)
expect(summary.contains("storage=nvme")).to_equal(true)
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 desktop driver completion marker contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
