# Wm Runtime Bridge Specification

> Tests covering SimpleOS WM runtime bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Runtime Bridge Specification

## Scenarios

### SimpleOS WM runtime bridge

#### maps framebuffer taskbar pointer hits to launcher commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps framebuffer taskbar pointer hits to launcher commands
   - Expected: command.kind equals `launcher_launch`
   - Expected: command.app_id equals `browser`
   - Expected: command.handled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps framebuffer taskbar pointer hits to launcher commands")
val command = simpleos_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("launcher_launch")
expect(command.app_id).to_equal("browser")
expect(command.handled).to_equal(true)
```

</details>

#### applies running-window focus and titlebar drag state

- applies running-window focus and titlebar drag state
   - Expected: focused.focused_window_id equals `win1`
   - Expected: dragging.focused_window_id equals `win2`
   - Expected: dragging.dragging_surface_id equals `surf2`
   - Expected: dragging.last_command_kind equals `window_drag_begin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies running-window focus and titlebar drag state")
val focused = simpleos_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
val dragging = simpleos_wm_apply_pointer(focused, _scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)

expect(focused.focused_window_id).to_equal("win1")
expect(dragging.focused_window_id).to_equal("win2")
expect(dragging.dragging_surface_id).to_equal("surf2")
expect(dragging.last_command_kind).to_equal("window_drag_begin")
```

</details>

#### emits serial-friendly command markers for QEMU capture checks

- emits serial-friendly command markers for QEMU capture checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits serial-friendly command markers for QEMU capture checks")
val marker = simpleos_wm_pointer_runtime_marker(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)
expect(marker).to_contain("[simpleos-wm] command=command_lane_icon")
expect(marker).to_contain("target=right_icon_1")
expect(marker).to_contain("handled=true")
```

</details>

<details>
<summary>Advanced: emits event-loop step markers for direct shell-loop invocation</summary>

#### emits event-loop step markers for direct shell-loop invocation

- emits event-loop step markers for direct shell-loop invocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits event-loop step markers for direct shell-loop invocation")
val marker = simpleos_wm_event_loop_marker(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
expect(marker).to_contain("[simpleos-wm] loop-step command=window_focus")
expect(marker).to_contain("window=win1")
expect(marker).to_contain("handled=true")
```

</details>


</details>

#### maps framebuffer taskbar secondary clicks to pin commands

- maps framebuffer taskbar secondary clicks to pin commands
   - Expected: command.kind equals `unpin_app`
   - Expected: command.app_id equals `browser`
   - Expected: pin.kind equals `pin_app`
   - Expected: pin.app_id equals `demo.app`
   - Expected: state.last_command_kind equals `unpin_app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps framebuffer taskbar secondary clicks to pin commands")
val command = simpleos_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)
val pin = simpleos_wm_pointer_runtime_command(_scene(), _taskbar(), 120, 575, "right", "down", 1000, "09:41", 2)
val state = simpleos_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)

expect(command.kind).to_equal("unpin_app")
expect(command.app_id).to_equal("browser")
expect(pin.kind).to_equal("pin_app")
expect(pin.app_id).to_equal("demo.app")
expect(state.last_command_kind).to_equal("unpin_app")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/wm_runtime_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS WM runtime bridge.
- SimpleOS WM runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `d5bd258ae7889c536c31a7f52cc2fbe60f07ee02f56cd117b48fc27f2b166c93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5bd258ae7889c536c31a7f52cc2fbe60f07ee02f56cd117b48fc27f2b166c93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5bd258ae7889c536c31a7f52cc2fbe60f07ee02f56cd117b48fc27f2b166c93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/desktop/wm_runtime_bridge_spec.spl
mirror: doc/06_spec/unit/os/desktop/wm_runtime_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/desktop/wm_runtime_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/desktop/wm_runtime_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/desktop/wm_runtime_bridge_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps framebuffer taskbar pointer hits to launcher commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/wm_runtime_bridge_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies running-window focus and titlebar drag state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/wm_runtime_bridge_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits serial-friendly command markers for QEMU capture checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
