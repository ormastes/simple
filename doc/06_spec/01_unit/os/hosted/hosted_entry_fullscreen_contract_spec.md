# Hosted Entry Fullscreen Contract Specification

> Tests covering hosted WM native fullscreen adapter contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Entry Fullscreen Contract Specification

## Scenarios

### hosted WM native fullscreen adapter contract

#### routes F11 through native borderless display state without internal maximize

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes F11 through native borderless display state without internal maximize


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes F11 through native borderless display state without internal maximize")
val source = file_read("src/os/hosted/hosted_entry.spl")
expect(source).to_contain("val KEY_F11: i64 = 122")
expect(source).to_contain("winit_window_set_fullscreen(native, on)")
expect(source).to_contain("request_display_mode(surface, target, nonce, now_micros)")
expect(source).to_contain("elif keycode == KEY_F11:")
expect(source).to_contain("surface = _request_host_fullscreen(surface, win, display_nonce, now_micros)")
```

</details>

#### correlates physical resize and scale observations with HostSurfaceState

- correlates physical resize and scale observations with HostSurfaceState


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("correlates physical resize and scale observations with HostSurfaceState")
val source = file_read("src/os/hosted/hosted_entry.spl")
expect(source).to_contain("kind == EVT_RESIZE or kind == EVT_SCALE_FACTOR")
expect(source).to_contain("ack_surface_event(surface, surface.request_nonce, physical, now_micros)")
expect(source).to_contain("comp.resize(physical.width, physical.height)")
expect(source).to_contain("winit_window_scale_factor(native)")
```

</details>

#### fails closed on transition timeout and close

- fails closed on transition timeout and close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on transition timeout and close")
val source = file_read("src/os/hosted/hosted_entry.spl")
expect(source).to_contain("now_micros > surface.deadline_micros")
expect(source).to_contain("fail_or_timeout_display_transition(surface, surface.request_nonce, \"\", now_micros)")
expect(source).to_contain("window closed during display transition")
expect(source).to_contain("display-transition-failed")
```

</details>

#### preserves native window coordinates and restores them after exit acknowledgement

- preserves native window coordinates and restores them after exit acknowledgement


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves native window coordinates and restores them after exit acknowledgement")
val source = file_read("src/os/hosted/hosted_entry.spl")
expect(source).to_contain("val EVT_MOVE: i64 = 2")
expect(source).to_contain("winit_event_window_position(ev)")
expect(source).to_contain("surface.saved_windowed_geometry.x = position.x")
expect(source).to_contain("surface.phase == HostDisplayTransitionPhase.Applied and surface.mode == HostDisplayMode.Windowed")
expect(source).to_contain("_restore_windowed_position(surface, win)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted WM native fullscreen adapter contract.
- hosted WM native fullscreen adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `999c66842f38f78e96f5641a37626fcb08820ffa00feb26279f7e1f462fb347f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `999c66842f38f78e96f5641a37626fcb08820ffa00feb26279f7e1f462fb347f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `999c66842f38f78e96f5641a37626fcb08820ffa00feb26279f7e1f462fb347f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.spl
mirror: doc/06_spec/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes F11 through native borderless display state without internal maximize' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'correlates physical resize and scale observations with HostSurfaceState' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/hosted/hosted_entry_fullscreen_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on transition timeout and close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
