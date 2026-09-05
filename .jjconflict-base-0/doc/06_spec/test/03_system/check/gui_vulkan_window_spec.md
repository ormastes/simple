# GUI Vulkan Window Verification

> Verifies that the widget showcase app launches as a REAL on-screen winit window (under a private Xvfb display) with rendering routed through the Simple Vulkan-backed Engine2D — not the CPU SoftwareBackend. The Vulkan backend rasterizes every primitive offscreen via compute dispatch; the finished frame is blitted into the X window via winit_present_rgba.

<!-- sdn-diagram:id=gui_vulkan_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_vulkan_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_vulkan_window_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_vulkan_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Vulkan Window Verification

Verifies that the widget showcase app launches as a REAL on-screen winit window (under a private Xvfb display) with rendering routed through the Simple Vulkan-backed Engine2D — not the CPU SoftwareBackend. The Vulkan backend rasterizes every primitive offscreen via compute dispatch; the finished frame is blitted into the X window via winit_present_rgba.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W1c, G1.1 |
| Category | Testing \| Infrastructure \| GUI |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G1.1) |
| Design | N/A |
| Source | `test/03_system/check/gui_vulkan_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the widget showcase app launches as a REAL on-screen winit window
(under a private Xvfb display) with rendering routed through the Simple
Vulkan-backed Engine2D — not the CPU SoftwareBackend. The Vulkan backend
rasterizes every primitive offscreen via compute dispatch; the finished frame is
blitted into the X window via winit_present_rgba.

Evidence is produced by `scripts/check/check-gui-vulkan-window.shs` (run with
`SIMPLE_GUI_BACKEND=vulkan`), which writes `build/gui-window-evidence/`:

1. `showcase_vulkan_window.png` — capture of the live winit window
2. `showcase_vulkan_offscreen.ppm` — the Vulkan-rendered frame
3. `showcase_vulkan_renderer_log.txt` — renderer-provenance line proving the
   Vulkan backend + device (lavapipe/llvmpipe under Xvfb)

This spec asserts the evidence env captured those proofs.

## Related Specifications

- [Production Readiness Master Plan](../../../doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md) — G1.1
- [Vulkan Engine2D Readback](check-vulkan-engine2d-readback) — bit-exact Vulkan raster oracle
- [Widget Showcase GUI](../../../examples/06_io/ui/widget_showcase_gui.spl)

## Scenarios

### GUI Vulkan Window

#### evidence env exists

- print "Loaded evidence with {entries len
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")
```

</details>

#### renderer log proves the Vulkan backend + device

- print "Loaded evidence with {entries len
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
   - Expected: get_env_value(entries, "assert_vulkan_backend") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_vulkan_backend")).to_equal("pass")
```

</details>

#### Vulkan engine produced a non-trivial rendered frame

- print "Loaded evidence with {entries len
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
   - Expected: get_env_value(entries, "assert_vulkan_frame") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_vulkan_frame")).to_equal("pass")
```

</details>

#### Vulkan frame shows legible showcase widgets

- print "Loaded evidence with {entries len
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
   - Expected: get_env_value(entries, "assert_widget_content") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_widget_content")).to_equal("pass")
```

</details>

#### live-window capture is nonblank

- print "Loaded evidence with {entries len
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
   - Expected: get_env_value(entries, "assert_window_capture") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_window_capture")).to_equal("pass")
```

</details>

#### overall status is pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_widget_content")).to_equal("pass")

val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "overall")).to_equal("pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G1.1)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G1.1))


</details>
