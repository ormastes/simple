# Wm Runtime Bridge Specification

> Tests covering host web WM runtime bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Runtime Bridge Specification

## Scenarios

### host web WM runtime bridge

#### maps host pointer hits on taskbar pins to launcher commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps host pointer hits on taskbar pins to launcher commands
   - Expected: command.kind equals `launcher_launch`
   - Expected: command.app_id equals `browser`
   - Expected: command.handled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps host pointer hits on taskbar pins to launcher commands")
val command = host_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("launcher_launch")
expect(command.app_id).to_equal("browser")
expect(command.handled).to_equal(true)
```

</details>

#### maps host pointer hits on running taskbar entries to focus commands

- maps host pointer hits on running taskbar entries to focus commands
   - Expected: command.kind equals `window_focus`
   - Expected: command.window_id equals `win1`
   - Expected: command.app_id equals `demo.app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps host pointer hits on running taskbar entries to focus commands")
val command = host_wm_pointer_runtime_command(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("window_focus")
expect(command.window_id).to_equal("win1")
expect(command.app_id).to_equal("demo.app")
```

</details>

#### maps host pointer hits on titlebars and command lane icons

- maps host pointer hits on titlebars and command lane icons
   - Expected: drag.kind equals `window_drag_begin`
   - Expected: drag.target_id equals `surf2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps host pointer hits on titlebars and command lane icons")
val drag = host_wm_pointer_runtime_command(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)
val icon_wire = host_wm_pointer_runtime_wire(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)

expect(drag.kind).to_equal("window_drag_begin")
expect(drag.target_id).to_equal("surf2")
expect(icon_wire).to_contain("kind=command_lane_icon")
expect(icon_wire).to_contain("target=right_icon_1")
```

</details>

#### maps host taskbar secondary clicks to pin commands

- maps host taskbar secondary clicks to pin commands
   - Expected: unpin.kind equals `unpin_app`
   - Expected: unpin.app_id equals `browser`
   - Expected: pin.kind equals `pin_app`
   - Expected: pin.app_id equals `demo.app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps host taskbar secondary clicks to pin commands")
val unpin = host_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)
val pin = host_wm_pointer_runtime_command(_scene(), _taskbar(), 120, 575, "right", "down", 1000, "09:41", 2)
expect(unpin.kind).to_equal("unpin_app")
expect(unpin.app_id).to_equal("browser")
expect(pin.kind).to_equal("pin_app")
expect(pin.app_id).to_equal("demo.app")
```

</details>

<details>
<summary>Advanced: applies host event-loop pointer steps to shared shell state</summary>

#### applies host event-loop pointer steps to shared shell state

- applies host event-loop pointer steps to shared shell state
   - Expected: launched.launched_apps.len() equals `1`
   - Expected: launched.launched_apps[0] equals `browser`
   - Expected: focused.focused_window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies host event-loop pointer steps to shared shell state")
val launched = host_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
val focused = host_wm_apply_pointer(launched, _scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
val marker = host_wm_event_loop_marker(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)

expect(launched.launched_apps.len()).to_equal(1)
expect(launched.launched_apps[0]).to_equal("browser")
expect(focused.focused_window_id).to_equal("win1")
expect(marker).to_contain("[host-wm] loop-step command=window_drag_begin")
expect(marker).to_contain("target=surf2")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/wm_runtime_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host web WM runtime bridge.
- host web WM runtime bridge

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

- Canonical SPipe generation for source `71080548db71e274e78d5837467338ab3becf9f054e0d6f68d04f542814cbcac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71080548db71e274e78d5837467338ab3becf9f054e0d6f68d04f542814cbcac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71080548db71e274e78d5837467338ab3becf9f054e0d6f68d04f542814cbcac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/ui/wm_runtime_bridge_spec.spl
mirror: doc/06_spec/unit/app/ui/wm_runtime_bridge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/wm_runtime_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/wm_runtime_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/wm_runtime_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/wm_runtime_bridge_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps host pointer hits on taskbar pins to launcher commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/wm_runtime_bridge_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps host pointer hits on running taskbar entries to focus commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/wm_runtime_bridge_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps host pointer hits on titlebars and command lane icons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
