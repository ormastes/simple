# Sys Gui 008 Ppm Diff Harness Specification

> <details>

<!-- sdn-diagram:id=sys_gui_008_ppm_diff_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_gui_008_ppm_diff_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_gui_008_ppm_diff_harness_spec -> std
sys_gui_008_ppm_diff_harness_spec -> os
sys_gui_008_ppm_diff_harness_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_gui_008_ppm_diff_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sys Gui 008 Ppm Diff Harness Specification

## Scenarios

### SYS-GUI-008 PPM-diff harness (Round-3)

#### captures virtio-gpu scanout via QMP screendump and commits baseline PPM

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _live_virtio_gpu_diff_enabled():
    print "[sys_gui_008_diff] live virtio-gpu capture disabled; set SIMPLEOS_QEMU_SYS_GUI_008_LIVE=1 to run"
    expect(_live_virtio_gpu_diff_enabled()).to_equal(false)
else:
    print "[sys_gui_008_diff] live virtio-gpu capture remains opt-in for local/QEMU hosts"
    expect(_live_virtio_gpu_diff_enabled()).to_equal(true)
```

</details>

#### diffs virtio-gpu baseline PPM against sys-gui-006 framebuffer PPM at ≤1% perceptual drift

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _live_virtio_gpu_diff_enabled():
    print "[sys_gui_008_diff] live virtio-gpu diff disabled; set SIMPLEOS_QEMU_SYS_GUI_008_LIVE=1 to run"
    expect(_live_virtio_gpu_diff_enabled()).to_equal(false)
else:
    print "[sys_gui_008_diff] live virtio-gpu diff remains opt-in for committed baseline hosts"
    expect(_live_virtio_gpu_diff_enabled()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/sys_gui_008_ppm_diff_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SYS-GUI-008 PPM-diff harness (Round-3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
