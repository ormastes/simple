# GUI Vulkan Window Verification

> Verifies that the widget showcase app launches as a REAL on-screen winit window (under a private Xvfb display) with rendering routed through the Simple Vulkan-backed Engine2D — not the CPU SoftwareBackend. The Vulkan backend rasterizes every primitive offscreen via compute dispatch; the finished frame is blitted into the X window via winit_present_rgba.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evidence env exists
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evidence env exists")
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

- evidence env exists
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
- renderer log proves the Vulkan backend + device
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "assert_vulkan_backend") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evidence env exists")
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

# @req REQ-SSPEC-SYSTEM
step("renderer log proves the Vulkan backend + device")
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_vulkan_backend")).to_equal("pass")
```

</details>

#### Vulkan engine produced a non-trivial rendered frame

- evidence env exists
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
- Vulkan engine produced a non-trivial rendered frame
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "assert_vulkan_frame") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evidence env exists")
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

# @req REQ-SSPEC-SYSTEM
step("Vulkan engine produced a non-trivial rendered frame")
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_vulkan_frame")).to_equal("pass")
```

</details>

#### Vulkan frame shows legible showcase widgets

- evidence env exists
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
- Vulkan frame shows legible showcase widgets
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "assert_widget_content") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evidence env exists")
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

# @req REQ-SSPEC-SYSTEM
step("Vulkan frame shows legible showcase widgets")
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_widget_content")).to_equal("pass")
```

</details>

#### live-window capture is nonblank

- evidence env exists
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "check") equals `gui_vulkan_window`
- live-window capture is nonblank
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: get_env_value(entries, "assert_window_capture") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evidence env exists")
val result = read_evidence_env(EV)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-gui-vulkan-window.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "check")).to_equal("gui_vulkan_window")

# @req REQ-SSPEC-SYSTEM
step("live-window capture is nonblank")
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_window_capture")).to_equal("pass")
```

</details>

#### overall status is pass

- Vulkan frame shows legible showcase widgets
   - Expected: get_env_value(entries, "assert_widget_content") equals `pass`
- overall status is pass
   - Expected: get_env_value(entries, "overall") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Vulkan frame shows legible showcase widgets")
val result = read_evidence_env(EV)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "assert_widget_content")).to_equal("pass")

# @req REQ-SSPEC-SYSTEM
step("overall status is pass")
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

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G1.1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `162b1f64d94242345972e395cb7d1f4c41c25171a96fa688744846a9208857f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `162b1f64d94242345972e395cb7d1f4c41c25171a96fa688744846a9208857f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `162b1f64d94242345972e395cb7d1f4c41c25171a96fa688744846a9208857f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/gui_vulkan_window_spec.spl
mirror: doc/06_spec/03_system/check/gui_vulkan_window_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_vulkan_window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_vulkan_window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_vulkan_window_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evidence env exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_vulkan_window_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renderer log proves the Vulkan backend + device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_vulkan_window_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Vulkan engine produced a non-trivial rendered frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
