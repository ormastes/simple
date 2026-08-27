# virtio_snd_device_spec

> Pure-Simple VirtIO sound owns bounded streams completions resets and events.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# virtio_snd_device_spec

Pure-Simple VirtIO sound owns bounded streams completions resets and events.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/virtio_snd_device_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure-Simple VirtIO sound owns bounded streams completions resets and events.

## Scenarios

### pure-Simple VirtIO sound device

#### negotiates prepares starts and emits ordered playback completion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- negotiates prepares starts and emits ordered playback completion
   - Expected: device.negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1).status equals `accepted`
   - Expected: device.prepare(playback_request()).status equals `prepared`
   - Expected: device.start().status equals `accepted`
   - Expected: submitted.status equals `submitted`
   - Expected: device.complete(submitted.sequence, submitted.generation, 256, "playback", 100u64).status equals `completed`
   - Expected: events.len() equals `1`
   - Expected: events[0].kind equals `playback-period`
   - Expected: events[0].correlation_id equals `submitted.sequence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negotiates prepares starts and emits ordered playback completion")
var device = VirtioSndDevice.create(8, 4)
expect(device.negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1).status).to_equal("accepted")
expect(device.prepare(playback_request()).status).to_equal("prepared")
expect(device.start().status).to_equal("accepted")
val submitted = device.submit("playback")
expect(submitted.status).to_equal("submitted")
expect(device.complete(submitted.sequence, submitted.generation, 256, "playback", 100u64).status).to_equal("completed")
val events = device.events.drain()
expect(events.len()).to_equal(1)
expect(events[0].kind).to_equal("playback-period")
expect(events[0].correlation_id).to_equal(submitted.sequence)
```

</details>

#### rejects invalid lifecycle direction and stale completion

- rejects invalid lifecycle direction and stale completion
   - Expected: device.prepare(playback_request()).status equals `not-negotiated`
   - Expected: device.submit("playback").status equals `invalid-state`
   - Expected: device.submit("sideways").status equals `invalid-direction`
   - Expected: device.complete(submitted.sequence, submitted.generation + 1u64, 256, "playback", 100u64).status equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid lifecycle direction and stale completion")
var device = VirtioSndDevice.create(4, 2)
expect(device.prepare(playback_request()).status).to_equal("not-negotiated")
device.negotiate(VIRTIO_SND_F_PCM_INFO, 1, 0)
device.prepare(playback_request())
expect(device.submit("playback").status).to_equal("invalid-state")
device.start()
expect(device.submit("sideways").status).to_equal("invalid-direction")
val submitted = device.submit("playback")
expect(device.complete(submitted.sequence, submitted.generation + 1u64, 256, "playback", 100u64).status).to_equal("stale-generation")
```

</details>

#### bounds outstanding periods records xrun and releases on reset shutdown

- bounds outstanding periods records xrun and releases on reset shutdown
   - Expected: device.submit("playback").status equals `queue-full`
   - Expected: device.xrun_count equals `1`
   - Expected: device.reset(200u64).outstanding equals `0`
   - Expected: device.shutdown(300u64).status equals `completed`
   - Expected: device.outstanding equals `0`
   - Expected: device.negotiated is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bounds outstanding periods records xrun and releases on reset shutdown")
var device = VirtioSndDevice.create(4, 2)
device.negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1)
device.prepare(playback_request())
device.start()
device.submit("playback")
device.submit("playback")
expect(device.submit("playback").status).to_equal("queue-full")
expect(device.xrun_count).to_equal(1)
expect(device.reset(200u64).outstanding).to_equal(0)
expect(device.shutdown(300u64).status).to_equal("completed")
expect(device.outstanding).to_equal(0)
expect(device.negotiated).to_equal(false)
```

</details>

#### routes hardware jack period and xrun interrupts into ordered events

- routes hardware jack period and xrun interrupts into ordered events
   - Expected: device.handle_hardware_event(VIRTIO_SND_EVT_JACK_CONNECTED, 4u32, 90u64).status equals `published`
   - Expected: device.handle_hardware_event(VIRTIO_SND_EVT_PCM_PERIOD_ELAPSED, 2u32, 100u64).status equals `published`
   - Expected: device.handle_hardware_event(VIRTIO_SND_EVT_PCM_XRUN, 2u32, 110u64).status equals `published`
   - Expected: device.handle_hardware_event(VIRTIO_SND_EVT_PCM_XRUN, 9u32, 120u64).status equals `stale-stream`
   - Expected: events.len() equals `3`
   - Expected: events[0].kind equals `audio-jack-connected`
   - Expected: events[1].kind equals `audio-period-elapsed`
   - Expected: events[2].kind equals `audio-xrun`
   - Expected: device.xrun_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes hardware jack period and xrun interrupts into ordered events")
var device = VirtioSndDevice.create(8, 4)
device.negotiate(VIRTIO_SND_F_PCM_INFO, 1, 1)
device.prepare(playback_request())
device.start()
expect(device.handle_hardware_event(VIRTIO_SND_EVT_JACK_CONNECTED, 4u32, 90u64).status).to_equal("published")
expect(device.handle_hardware_event(VIRTIO_SND_EVT_PCM_PERIOD_ELAPSED, 2u32, 100u64).status).to_equal("published")
expect(device.handle_hardware_event(VIRTIO_SND_EVT_PCM_XRUN, 2u32, 110u64).status).to_equal("published")
expect(device.handle_hardware_event(VIRTIO_SND_EVT_PCM_XRUN, 9u32, 120u64).status).to_equal("stale-stream")
val events = device.events.drain()
expect(events.len()).to_equal(3)
expect(events[0].kind).to_equal("audio-jack-connected")
expect(events[1].kind).to_equal("audio-period-elapsed")
expect(events[2].kind).to_equal("audio-xrun")
expect(device.xrun_count).to_equal(1)
```

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
- `REQ-001`
- `REQ-003`
- `REQ-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a923663d6ca83c8b0eedc4caef6e63a38df318a208ff23f62284111bdebf5f28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a923663d6ca83c8b0eedc4caef6e63a38df318a208ff23f62284111bdebf5f28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a923663d6ca83c8b0eedc4caef6e63a38df318a208ff23f62284111bdebf5f28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/virtio_snd_device_spec.spl
mirror: doc/06_spec/03_system/io_audio/virtio_snd_device_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/virtio_snd_device_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/virtio_snd_device_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/virtio_snd_device_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/virtio_snd_device_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/virtio_snd_device_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negotiates prepares starts and emits ordered playback completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/virtio_snd_device_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid lifecycle direction and stale completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/virtio_snd_device_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds outstanding periods records xrun and releases on reset shutdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
