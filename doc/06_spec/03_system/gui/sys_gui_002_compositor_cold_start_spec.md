# Sys Gui 002 Compositor Cold Start Specification

> <details>

<!-- sdn-diagram:id=sys_gui_002_compositor_cold_start_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_gui_002_compositor_cold_start_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_gui_002_compositor_cold_start_spec -> std
sys_gui_002_compositor_cold_start_spec -> os
sys_gui_002_compositor_cold_start_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_gui_002_compositor_cold_start_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sys Gui 002 Compositor Cold Start Specification

## Scenarios

### SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002)

#### builds desktop_e2e_entry.spl into a baremetal kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop, captures compositor-cold-start frame, matches baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not _live_compositor_cold_start_capture_enabled():
    print "[sys_gui_002_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_SYS_GUI_002_LIVE=1 to run"
    expect(_live_compositor_cold_start_capture_enabled()).to_equal(false)
else:
    val qemu_available = can_run_target(target)
    if not qemu_available:
        print "[sys_gui_002_spec] qemu-system-x86_64 not available, skipping live capture"
        expect(qemu_available).to_equal(false)
    else:
        expect(_run_live_compositor_cold_start_capture(target)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/sys_gui_002_compositor_cold_start_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
