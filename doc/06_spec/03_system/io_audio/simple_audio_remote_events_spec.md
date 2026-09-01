# simple_audio_remote_events_spec

> Remote CUDA, fallback and reset use the shared ordered device-event path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_remote_events_spec

Remote CUDA, fallback and reset use the shared ordered device-event path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_remote_events_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Remote CUDA, fallback and reset use the shared ordered device-event path.

## Scenarios

### remote audio shared device events

#### publishes accepted CUDA readback as an ordered audio period

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes accepted CUDA readback as an ordered audio period
   - Expected: result.publish_status equals `published`
   - Expected: result.accepted_device_result is true
   - Expected: drained.len() equals `1`
   - Expected: drained[0].sequence equals `1u64`
   - Expected: drained[0].kind equals `audio-period`
   - Expected: drained[0].status equals `remote-host-cuda-readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes accepted CUDA readback as an ordered audio period")
var events = SimpleDeviceEventRing.create(4)
val result = simple_audio_publish_remote_event(events, 100u64, 256u64, 4, 1, 71u64, "accepted-device-result")
expect(result.publish_status).to_equal("published")
expect(result.accepted_device_result).to_equal(true)
val drained = events.drain()
expect(drained.len()).to_equal(1)
expect(drained[0].sequence).to_equal(1u64)
expect(drained[0].kind).to_equal("audio-period")
expect(drained[0].status).to_equal("remote-host-cuda-readback")
```

</details>

#### keeps fallback and reset monotonic on the same event stream

- keeps fallback and reset monotonic on the same event stream
   - Expected: fallback.cpu_fallback is true
   - Expected: reset.event_kind equals `device-reset`
   - Expected: drained.len() equals `2`
   - Expected: drained[0].sequence equals `1u64`
   - Expected: drained[1].sequence equals `2u64`
   - Expected: drained[1].monotonic_ns equals `200u64`
   - Expected: drained[0].kind equals `audio-offload-fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps fallback and reset monotonic on the same event stream")
var events = SimpleDeviceEventRing.create(4)
val fallback = simple_audio_publish_remote_event(events, 200u64, 512u64, 4, 1, 72u64, "cpu-fallback-timeout")
val reset = simple_audio_publish_remote_event(events, 150u64, 0u64, 4, 1, 73u64, "device-reset")
expect(fallback.cpu_fallback).to_equal(true)
expect(reset.event_kind).to_equal("device-reset")
val drained = events.drain()
expect(drained.len()).to_equal(2)
expect(drained[0].sequence).to_equal(1u64)
expect(drained[1].sequence).to_equal(2u64)
expect(drained[1].monotonic_ns).to_equal(200u64)
expect(drained[0].kind).to_equal("audio-offload-fallback")
```

</details>

#### fails closed when the shared event ring is full or shut down

- fails closed when the shared event ring is full or shut down
   - Expected: full.publish_status equals `queue-full`
   - Expected: closed.publish_status equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when the shared event ring is full or shut down")
var events = SimpleDeviceEventRing.create(2)
simple_audio_publish_remote_event(events, 1u64, 0u64, 4, 1, 1u64, "pending")
simple_audio_publish_remote_event(events, 2u64, 0u64, 4, 1, 2u64, "pending")
val full = simple_audio_publish_remote_event(events, 3u64, 0u64, 4, 1, 3u64, "cpu-fallback-parity")
expect(full.publish_status).to_equal("queue-full")
events.shutdown(4u64, 4)
val closed = simple_audio_publish_remote_event(events, 5u64, 0u64, 4, 1, 4u64, "accepted-device-result")
expect(closed.publish_status).to_equal("shutdown")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-004`
- `REQ-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f9ee310e385b87f721ecfe930ea1323264331138a315724b801d143fd7e9014f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9ee310e385b87f721ecfe930ea1323264331138a315724b801d143fd7e9014f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9ee310e385b87f721ecfe930ea1323264331138a315724b801d143fd7e9014f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_remote_events_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_remote_events_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_remote_events_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_remote_events_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_remote_events_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_remote_events_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_remote_events_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes accepted CUDA readback as an ordered audio period' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_remote_events_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps fallback and reset monotonic on the same event stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_remote_events_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the shared event ring is full or shut down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
