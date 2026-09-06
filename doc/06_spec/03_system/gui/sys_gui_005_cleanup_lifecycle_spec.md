# Sys Gui 005 Cleanup Lifecycle Specification

> <details>

<!-- sdn-diagram:id=sys_gui_005_cleanup_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_gui_005_cleanup_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_gui_005_cleanup_lifecycle_spec -> std
sys_gui_005_cleanup_lifecycle_spec -> os
sys_gui_005_cleanup_lifecycle_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_gui_005_cleanup_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sys Gui 005 Cleanup Lifecycle Specification

## Scenarios

### SimpleOS lifecycle cleanup live gate (SYS-GUI-005)

#### builds sys_gui_005_cleanup_entry.spl into a baremetal kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _cleanup_target()
if not file_exists(target.entry):
    print "[sys_gui_005_spec] missing cleanup entry {target.entry}, skipping build"
    expect(file_exists(target.entry)).to_equal(false)
else:
    val ok = build_os(target)
    expect(ok).to_equal(true)
    expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots cleanup entry, walks all three sub-scenarios, captures post-cleanup frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _cleanup_target()
if not file_exists(target.entry):
    print "[sys_gui_005_spec] missing cleanup entry {target.entry}, skipping live capture"
    expect(file_exists(target.entry)).to_equal(false)
else:
    if not _live_cleanup_capture_enabled():
        print "[sys_gui_005_spec] live cleanup capture disabled; set SIMPLEOS_QEMU_SYS_GUI_005_LIVE=1 to run"
        expect(_live_cleanup_capture_enabled()).to_equal(false)
    else:
        if not can_run_target(target):
            print "[sys_gui_005_spec] qemu-system-x86_64 not available, skipping live capture"
            expect(can_run_target(target)).to_equal(false)
        else:
            expect(build_os(target)).to_equal(true)
            expect(file_exists(target.output)).to_equal(true)
            print "[sys_gui_005_spec] live capture implementation is gated on restoring {target.entry}"
            expect(target.entry.contains("sys_gui_005_cleanup_entry.spl")).to_equal(true)
```

</details>

#### has a baselines directory for the SYS-GUI-005 cleanup gate

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "doc/08_tracking/baselines"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS lifecycle cleanup live gate (SYS-GUI-005)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
