# Simple Wm Host Fullscreen Specification

> <details>

<!-- sdn-diagram:id=simple_wm_host_fullscreen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_wm_host_fullscreen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_wm_host_fullscreen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_wm_host_fullscreen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Wm Host Fullscreen Specification

## Scenarios

### Simple WM production host fullscreen

#### should restore windowed host geometry and preserve the exact internal scene after F11 fullscreen

- Launch the production WM in a host window
   - Artifact capture: after_step
- Interact with internal windows and taskbar chrome
   - Artifact capture: after_step
- Verify internal window and taskbar interactions reached the production scene
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: interaction equals `verified`
- Capture the exact windowed host and internal scene state
   - Artifact capture: after_step
- Toggle the host surface to fullscreen and acknowledge the matching nonce
   - Artifact capture: after_step
- Verify fullscreen acknowledgement matches the requested transition
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: entered equals `acknowledged-fullscreen`
- Validate the fullscreen capture and backend provenance
   - Artifact capture: after_step
- Verify fullscreen pixels and renderer provenance match the acknowledged state
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_correlated_host_capture(run_id, entered, "fullscreen") equals `verified`
- Toggle the host surface back to windowed and acknowledge the matching nonce
   - Artifact capture: after_step
- Verify windowed acknowledgement matches the restore transition
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: restored equals `acknowledged-windowed`
- Validate restored x y width height and exact internal snapshot preservation
   - Artifact capture: after_step
- Verify the complete internal scene is unchanged by physical mode transitions
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_exact_internal_snapshot_preserved(before, snapshot_after) equals `exact`
- Verify restored pixels geometry and renderer provenance are correlated
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_correlated_host_capture(run_id, restored, "windowed") equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Interact with internal windows and taskbar chrome")
val interaction = drive_host_window_and_taskbar_interactions(run_id)
step("Verify internal window and taskbar interactions reached the production scene")
expect(interaction).to_equal("verified")
step("Capture the exact windowed host and internal scene state")
val before = capture_exact_internal_scene_snapshot(run_id, "windowed-before")
step("Toggle the host surface to fullscreen and acknowledge the matching nonce")
val entered = press_f11_and_wait_for_physical_ack(run_id, "fullscreen")
step("Verify fullscreen acknowledgement matches the requested transition")
expect(entered).to_equal("acknowledged-fullscreen")
step("Validate the fullscreen capture and backend provenance")
step("Verify fullscreen pixels and renderer provenance match the acknowledged state")
expect(verify_correlated_host_capture(run_id, entered, "fullscreen")).to_equal("verified")
step("Toggle the host surface back to windowed and acknowledge the matching nonce")
val restored = press_f11_and_wait_for_physical_ack(run_id, "windowed")
step("Verify windowed acknowledgement matches the restore transition")
expect(restored).to_equal("acknowledged-windowed")
step("Validate restored x y width height and exact internal snapshot preservation")
val snapshot_after = capture_exact_internal_scene_snapshot(run_id, "windowed-after")
step("Verify the complete internal scene is unchanged by physical mode transitions")
expect(verify_exact_internal_snapshot_preserved(before, snapshot_after)).to_equal("exact")
step("Verify restored pixels geometry and renderer provenance are correlated")
expect(verify_correlated_host_capture(run_id, restored, "windowed")).to_equal("verified")
```

</details>

<details>
<summary>Advanced: should correlate every fullscreen request with its nonce phase and physical geometry</summary>

#### should correlate every fullscreen request with its nonce phase and physical geometry

- Launch the production WM in a host window
   - Protocol capture: after_step
- Request fullscreen and retain the request nonce and prior x y width height
   - Protocol capture: after_step
- Request windowed restore with a newer nonce
   - Protocol capture: after_step
- Validate captures against their matching acknowledged phases
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: verify_correlated_host_capture(run_id, entered, "fullscreen") equals `verified`
   - Expected: verify_correlated_host_capture(run_id, restored, "windowed") equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Request fullscreen and retain the request nonce and prior x y width height")
val entered = press_f11_and_wait_for_physical_ack(run_id, "fullscreen")
step("Request windowed restore with a newer nonce")
val restored = press_f11_and_wait_for_physical_ack(run_id, "windowed")
step("Validate captures against their matching acknowledged phases")
expect(verify_correlated_host_capture(run_id, entered, "fullscreen")).to_equal("verified")
expect(verify_correlated_host_capture(run_id, restored, "windowed")).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should roll back and fail closed for denied timed-out stale or reordered transitions</summary>

#### should roll back and fail closed for denied timed-out stale or reordered transitions

- Launch the production WM in a host window
   - Protocol capture: after_step
- Exercise denied timeout stale nonce and reordered acknowledgement cases
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: [denied, timed_out, stale, reordered] equals `["rolled-back", "rolled-back", "rejected", "rejected"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Exercise denied timeout stale nonce and reordered acknowledgement cases")
val denied = submit_host_transition_failure_case(run_id, "denied")
val timed_out = submit_host_transition_failure_case(run_id, "timeout")
val stale = submit_host_transition_failure_case(run_id, "stale-nonce")
val reordered = submit_host_transition_failure_case(run_id, "reordered-ack")
expect([denied, timed_out, stale, reordered]).to_equal(["rolled-back", "rolled-back", "rejected", "rejected"])
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale wrong-process or unverifiable captures</summary>

#### should reject missing stale wrong-process or unverifiable captures

- Launch the production WM in a host window
   - Artifact capture: after_step
- Submit missing stale wrong-process and revision-mismatched captures
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: submit_host_transition_failure_case(run_id, "capture-missing") equals `rejected`
   - Expected: submit_host_transition_failure_case(run_id, "capture-stale") equals `rejected`
   - Expected: submit_host_transition_failure_case(run_id, "capture-wrong-process") equals `rejected`
   - Expected: submit_host_transition_failure_case(run_id, "capture-revision-mismatch") equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Submit missing stale wrong-process and revision-mismatched captures")
expect(submit_host_transition_failure_case(run_id, "capture-missing")).to_equal("rejected")
expect(submit_host_transition_failure_case(run_id, "capture-stale")).to_equal("rejected")
expect(submit_host_transition_failure_case(run_id, "capture-wrong-process")).to_equal("rejected")
expect(submit_host_transition_failure_case(run_id, "capture-revision-mismatch")).to_equal("rejected")
```

</details>


</details>

<details>
<summary>Advanced: should measure ten warm cached pure-Simple launches to first shared-scene frame</summary>

#### should measure ten warm cached pure-Simple launches to first shared-scene frame

- Launch once and discard the cold production host sample
   - Exec capture: after_step
- Measure ten warm launches to the first presented shared-scene frame
   - Exec capture: after_step
- Validate every startup measurement and its provenance
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verify_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch once and discard the cold production host sample")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Measure ten warm launches to the first presented shared-scene frame")
val report = measure_warm_host_startup(run_id)
step("Validate every startup measurement and its provenance")
expect(verify_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should measure thirty acknowledged fullscreen enter and exit pairs</summary>

#### should measure thirty acknowledged fullscreen enter and exit pairs

- Launch the production WM in a host window
   - Exec capture: after_step
- Measure thirty nonce-correlated enter and exit pairs
   - Exec capture: after_step
- Compute nearest-rank p95 and validate measurement provenance
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verify_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Measure thirty nonce-correlated enter and exit pairs")
val report = measure_host_mode_pairs(run_id)
step("Compute nearest-rank p95 and validate measurement provenance")
expect(verify_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should bound RSS growth and slope across one hundred transition pairs</summary>

#### should bound RSS growth and slope across one hundred transition pairs

- Launch the production WM and record its stable baseline RSS
   - Exec capture: after_step
- Measure RSS after one hundred completed enter and exit pairs
   - Exec capture: after_step
- Validate final growth final-fifty slope and measurement provenance
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verify_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM and record its stable baseline RSS")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Measure RSS after one hundred completed enter and exit pairs")
val report = measure_host_rss_stability(run_id)
step("Validate final growth final-fifty slope and measurement provenance")
expect(verify_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple WM production host fullscreen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
