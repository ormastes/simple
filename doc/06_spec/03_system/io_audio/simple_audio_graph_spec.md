# simple_audio_graph_spec

> Direct, 2D, and 3D sound share one deterministic pure-Simple audio graph.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_graph_spec

Direct, 2D, and 3D sound share one deterministic pure-Simple audio graph.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_graph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct, 2D, and 3D sound share one deterministic pure-Simple audio graph.

## Scenarios

### Pure-Simple shared audio graph

#### executes bounded direct 2D and 3D graph transitions

- executes bounded direct 2D and 3D graph transitions
   - Expected: graph.submit_direct(format, 512).status equals `epoch-required`
   - Expected: graph.begin_epoch() equals `ready`
   - Expected: direct.status equals `rendered`
   - Expected: direct.route equals `direct`
   - Expected: spatial.status equals `rendered`
   - Expected: graph.submit_2d(format, 512, 0).status equals `queue-full`
   - Expected: graph.cancel(direct.source_id) equals `cancelled`
   - Expected: graph.submit_2d(format, 512, 500).status equals `rendered`
   - Expected: graph.shutdown() equals `2`
   - Expected: graph.live_source_count() equals `0`
   - Expected: graph.begin_epoch() equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes bounded direct 2D and 3D graph transitions")
var graph = SimpleAudioGraph.create(2)
val format = SimpleAudioFormat(sample_rate: 48000, channels: 2, period_frames: 256, sample_kind: "f32")
expect(graph.submit_direct(format, 512).status).to_equal("epoch-required")
expect(graph.begin_epoch()).to_equal("ready")
val direct = graph.submit_direct(format, 512)
val spatial = graph.submit_3d(format, 512, 1000, 1000, 100)
expect(direct.status).to_equal("rendered")
expect(direct.route).to_equal("direct")
expect(spatial.status).to_equal("rendered")
expect(spatial.metadata).to_contain("hrtf")
expect(graph.submit_2d(format, 512, 0).status).to_equal("queue-full")
expect(graph.cancel(direct.source_id)).to_equal("cancelled")
expect(graph.submit_2d(format, 512, 500).status).to_equal("rendered")
expect(graph.shutdown()).to_equal(2)
expect(graph.live_source_count()).to_equal(0)
expect(graph.begin_epoch()).to_equal("shutdown")
```

</details>

#### routes direct 2D and 3D sources through one graph epoch

- routes direct 2D and 3D sources through one graph epoch
   - Log capture: after_step
- Open the pure-Simple direct audio graph
   - Log capture: after_step
- Submit direct PCM and positioned Engine2D sound
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: result.direct_status equals `rendered`
   - Expected: result.engine2d_status equals `rendered`
- Submit a listener and spatial Engine3D source
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: result.engine3d_status equals `rendered`
   - Expected: result.graph_epoch_count equals `1`
- Verify spatial features and deterministic stereo fallback
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: result.stereo_fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes direct 2D and 3D sources through one graph epoch")
step("Open the pure-Simple direct audio graph")
val result = simple_audio_graph_operator_probe("direct-2d-3d")
step("Submit direct PCM and positioned Engine2D sound")
expect(result.direct_status).to_equal("rendered")
expect(result.engine2d_status).to_equal("rendered")
step("Submit a listener and spatial Engine3D source")
expect(result.engine3d_status).to_equal("rendered")
expect(result.graph_epoch_count).to_equal(1)
step("Verify spatial features and deterministic stereo fallback")
expect(result.spatial_features).to_contain("pan")
expect(result.spatial_features).to_contain("distance")
expect(result.spatial_features).to_contain("cone")
expect(result.spatial_features).to_contain("doppler")
expect(result.spatial_features).to_contain("occlusion")
expect(result.spatial_features).to_contain("hrtf")
expect(result.stereo_fallback).to_equal(true)
```

</details>

<details>
<summary>Advanced: reports bounded format lifecycle and stream faults</summary>

#### reports bounded format lifecycle and stream faults

- reports bounded format lifecycle and stream faults
- Negotiate valid and boundary audio formats
   - Expected: result.valid_format equals `accepted`
   - Expected: result.invalid_format equals `invalid-format`
- Exercise queue pressure cancellation device loss and xrun
   - Expected: result.queue_full equals `queue-full`
   - Expected: result.cancelled equals `cancelled`
   - Expected: result.device_lost equals `disconnected`
   - Expected: result.underrun_events equals `1`
   - Expected: result.overrun_events equals `1`
- Confirm ordered teardown emits no later event
   - Expected: result.shutdown_receipts equals `1`
   - Expected: result.post_shutdown_events equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports bounded format lifecycle and stream faults")
step("Negotiate valid and boundary audio formats")
val result = simple_audio_graph_fault_probe()
expect(result.valid_format).to_equal("accepted")
expect(result.invalid_format).to_equal("invalid-format")
step("Exercise queue pressure cancellation device loss and xrun")
expect(result.queue_full).to_equal("queue-full")
expect(result.cancelled).to_equal("cancelled")
expect(result.device_lost).to_equal("disconnected")
expect(result.underrun_events).to_equal(1)
expect(result.overrun_events).to_equal(1)
step("Confirm ordered teardown emits no later event")
expect(result.shutdown_receipts).to_equal(1)
expect(result.post_shutdown_events).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: releases every graph stream buffer and device resource</summary>

#### releases every graph stream buffer and device resource

- releases every graph stream buffer and device resource
- Create and retire graph plans across generation changes
   - Expected: result.stale_generation_status equals `stale-generation`
- Drain cancel and close the device
   - Expected: result.live_handles equals `0`
   - Expected: result.live_mappings equals `0`
   - Expected: result.live_buffers equals `0`
   - Expected: result.live_callbacks equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("releases every graph stream buffer and device resource")
step("Create and retire graph plans across generation changes")
val result = simple_audio_graph_resource_probe()
expect(result.stale_generation_status).to_equal("stale-generation")
step("Drain cancel and close the device")
expect(result.live_handles).to_equal(0)
expect(result.live_mappings).to_equal(0)
expect(result.live_buffers).to_equal(0)
expect(result.live_callbacks).to_equal(0)
```

</details>


</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-016`
- `REQ-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `663d6e01be2a948d2732bce353baad92ff0687911957eebb1bda3d76faabea8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `663d6e01be2a948d2732bce353baad92ff0687911957eebb1bda3d76faabea8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `663d6e01be2a948d2732bce353baad92ff0687911957eebb1bda3d76faabea8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_graph_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_graph_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_graph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_graph_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_graph_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_graph_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_graph_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded direct 2D and 3D graph transitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_graph_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes direct 2D and 3D sources through one graph epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_graph_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports bounded format lifecycle and stream faults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
