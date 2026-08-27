# Simple WM Host Fullscreen

> Launches the cached production pure-Simple host WM, drives its real input

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple WM Host Fullscreen

Launches the cached production pure-Simple host WM, drives its real input

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Launches the cached production pure-Simple host WM, drives its real input
surface from windowed mode through F11 fullscreen and back, and correlates the
physical transition with an unchanged internal `SharedWmScene` snapshot. The
runtime evidence must include executable, backend, transition, scene, frame,
and capture identities; unavailable or mismatched evidence fails closed.

The performance scenarios define the required NFR-1, NFR-2, and NFR-5 sample
methodology. They do not accept synthetic timings, source inspection, demo
entrypoints, Rust-seed provenance, or unverified screenshots as measurements.

## Scenarios

### Simple WM production host fullscreen

#### should restore windowed host geometry and preserve the exact internal scene after F11 fullscreen

- should restore windowed host geometry and preserve the exact internal scene after F11 fullscreen
   - Artifact capture: after_step
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

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore windowed host geometry and preserve the exact internal scene after F11 fullscreen")
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

- should correlate every fullscreen request with its nonce phase and physical geometry
   - Protocol capture: after_step
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should correlate every fullscreen request with its nonce phase and physical geometry")
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

- should roll back and fail closed for denied timed-out stale or reordered transitions
   - Protocol capture: after_step
- Launch the production WM in a host window
   - Protocol capture: after_step
- Exercise denied timeout stale nonce and reordered acknowledgement cases
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: [denied, timed_out, stale, reordered] equals `["rolled-back", "rolled-back", "rejected", "rejected"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should roll back and fail closed for denied timed-out stale or reordered transitions")
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

- should reject missing stale wrong-process or unverifiable captures
   - Artifact capture: after_step
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale wrong-process or unverifiable captures")
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

- should measure ten warm cached pure-Simple launches to first shared-scene frame
   - Exec capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should measure ten warm cached pure-Simple launches to first shared-scene frame")
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

- should measure thirty acknowledged fullscreen enter and exit pairs
   - Exec capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should measure thirty acknowledged fullscreen enter and exit pairs")
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

- should bound RSS growth and slope across one hundred transition pairs
   - Exec capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound RSS growth and slope across one hundred transition pairs")
step("Launch the production WM and record its stable baseline RSS")
val run_id = launch_production_cached_pure_simple_host_wm()
step("Measure RSS after one hundred completed enter and exit pairs")
val report = measure_host_rss_stability(run_id)
step("Validate final growth final-fifty slope and measurement provenance")
expect(verify_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-1`
- `REQ-5`
- `REQ-6`
- `REQ-7`
- `REQ-8`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28d54948c0055d5ac80668003da4fe535066710a612dcc11a6c04f6cd67e1e6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28d54948c0055d5ac80668003da4fe535066710a612dcc11a6c04f6cd67e1e6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28d54948c0055d5ac80668003da4fe535066710a612dcc11a6c04f6cd67e1e6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl
mirror: doc/06_spec/03_system/os/wm/simple_wm_host_fullscreen_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/wm/simple_wm_host_fullscreen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simple_wm_host_fullscreen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore windowed host geometry and preserve the exact internal scene after F11 fullscreen' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should correlate every fullscreen request with its nonce phase and physical geometry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should correlate every fullscreen request with its nonce phase and physical geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should roll back and fail closed for denied timed-out stale or reordered transitions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should roll back and fail closed for denied timed-out stale or reordered transitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:124:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale wrong-process or unverifiable captures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing stale wrong-process or unverifiable captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:137:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should measure ten warm cached pure-Simple launches to first shared-scene frame' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl:149:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should measure thirty acknowledged fullscreen enter and exit pairs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
