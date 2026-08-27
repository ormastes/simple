# Virtio Snd Protocol Specification

> Tests covering pure-Simple VirtIO sound protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Virtio Snd Protocol Specification

## Scenarios

### pure-Simple VirtIO sound protocol

#### encodes exact little-endian control request layouts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes exact little-endian control request layouts
   - Expected: info.len() equals `16`
   - Expected: info[0].to_i64() equals `0`
   - Expected: info[1].to_i64() equals `1`
   - Expected: params.len() equals `24`
   - Expected: params[20].to_i64() equals `2`
   - Expected: params[21].to_i64() equals `5`
   - Expected: params[22].to_i64() equals `7`
   - Expected: start.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes exact little-endian control request layouts")
val info = virtio_snd_pcm_info_query(2u32, 3u32)
val params = virtio_snd_pcm_set_params([
    1u32, 4096u32, 1024u32, 2u32,
    VIRTIO_SND_PCM_FMT_S16.to_u32(), VIRTIO_SND_PCM_RATE_48000.to_u32()
])
val start = virtio_snd_pcm_command(VIRTIO_SND_R_PCM_START, 1u32)
expect(info.len()).to_equal(16)
expect(info[0].to_i64()).to_equal(0)
expect(info[1].to_i64()).to_equal(1)
expect(params.len()).to_equal(24)
expect(params[20].to_i64()).to_equal(2)
expect(params[21].to_i64()).to_equal(5)
expect(params[22].to_i64()).to_equal(7)
expect(start.len()).to_equal(8)
```

</details>

#### maps device status without accepting unknown values

- maps device status without accepting unknown values
   - Expected: virtio_snd_status_name(VIRTIO_SND_S_OK) equals `ok`
   - Expected: virtio_snd_status_name(VIRTIO_SND_S_NOT_SUPP) equals `unsupported`
   - Expected: virtio_snd_status_name(0xDEADu32) equals `unknown-status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps device status without accepting unknown values")
expect(virtio_snd_status_name(VIRTIO_SND_S_OK)).to_equal("ok")
expect(virtio_snd_status_name(VIRTIO_SND_S_NOT_SUPP)).to_equal("unsupported")
expect(virtio_snd_status_name(0xDEADu32)).to_equal("unknown-status")
```

</details>

#### decodes jack period and xrun event payloads

- decodes jack period and xrun event payloads
   - Expected: jack.kind equals `audio-jack-connected`
   - Expected: jack.target_id equals `3`
   - Expected: period.status equals `completed`
   - Expected: xrun.status equals `xrun`
   - Expected: virtio_snd_decode_event(0xFFFFu32, 0u32).status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("decodes jack period and xrun event payloads")
val jack = virtio_snd_decode_event(VIRTIO_SND_EVT_JACK_CONNECTED, 3u32)
val period = virtio_snd_decode_event(VIRTIO_SND_EVT_PCM_PERIOD_ELAPSED, 2u32)
val xrun = virtio_snd_decode_event(VIRTIO_SND_EVT_PCM_XRUN, 2u32)
expect(jack.kind).to_equal("audio-jack-connected")
expect(jack.target_id).to_equal(3)
expect(period.status).to_equal("completed")
expect(xrun.status).to_equal("xrun")
expect(virtio_snd_decode_event(0xFFFFu32, 0u32).status).to_equal("unsupported")
```

</details>

#### negotiates bounded playback and capture capabilities

- negotiates bounded playback and capture capabilities
   - Expected: result.status equals `accepted`
   - Expected: result.playback is true
   - Expected: result.capture is true
   - Expected: result.accepted_features equals `VIRTIO_SND_F_PCM_INFO | VIRTIO_SND_F_CHMAP_INFO`
   - Expected: virtio_snd_negotiate(0u64, 0, 0).status equals `unsupported`
   - Expected: virtio_snd_negotiate(0u64, -1, 0).status equals `malformed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("negotiates bounded playback and capture capabilities")
val result = virtio_snd_negotiate(VIRTIO_SND_F_PCM_INFO | VIRTIO_SND_F_CHMAP_INFO, 1, 1)
expect(result.status).to_equal("accepted")
expect(result.playback).to_equal(true)
expect(result.capture).to_equal(true)
expect(result.accepted_features).to_equal(VIRTIO_SND_F_PCM_INFO | VIRTIO_SND_F_CHMAP_INFO)
expect(virtio_snd_negotiate(0u64, 0, 0).status).to_equal("unsupported")
expect(virtio_snd_negotiate(0u64, -1, 0).status).to_equal("malformed")
```

</details>

#### validates period and DMA bounds

- validates period and DMA bounds
   - Expected: valid.status equals `accepted`
   - Expected: valid.period_bytes equals `1920`
   - Expected: valid.buffer_bytes equals `7680`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: -1, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-stream`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "bad", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-direction`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 0, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-format`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1000)).status equals `invalid-buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("validates period and DMA bounds")
val valid = virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920))
expect(valid.status).to_equal("accepted")
expect(valid.period_bytes).to_equal(1920)
expect(valid.buffer_bytes).to_equal(7680)
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: -1, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-stream")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "bad", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-direction")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 0, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-format")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1000)).status).to_equal("invalid-buffer")
```

</details>

#### enforces stream lifecycle and generation invalidation

- enforces stream lifecycle and generation invalidation
   - Expected: prepared.next_state equals `prepared`
   - Expected: prepared.generation equals `4u64`
   - Expected: virtio_snd_stream_transition("prepared", "start", 4u64).next_state equals `running`
   - Expected: virtio_snd_stream_transition("running", "release", 4u64).status equals `invalid-state`
   - Expected: lost.status equals `disconnected`
   - Expected: lost.generation equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("enforces stream lifecycle and generation invalidation")
val prepared = virtio_snd_stream_transition("closed", "prepare", 3u64)
expect(prepared.next_state).to_equal("prepared")
expect(prepared.generation).to_equal(4u64)
expect(virtio_snd_stream_transition("prepared", "start", 4u64).next_state).to_equal("running")
expect(virtio_snd_stream_transition("running", "release", 4u64).status).to_equal("invalid-state")
val lost = virtio_snd_stream_transition("running", "device-lost", 4u64)
expect(lost.status).to_equal("disconnected")
expect(lost.generation).to_equal(5u64)
```

</details>

#### rejects stale and malformed completions

- rejects stale and malformed completions
   - Expected: ok.status equals `completed`
   - Expected: ok.kind equals `playback-period`
   - Expected: ok.sequence equals `7u64`
   - Expected: virtio_snd_completion(8u64, 0, 4u64, 3u64, 480, "capture").status equals `stale-generation`
   - Expected: virtio_snd_completion(9u64, 0, 4u64, 4u64, -1, "capture").status equals `malformed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects stale and malformed completions")
val ok = virtio_snd_completion(7u64, 0, 4u64, 4u64, 480, "playback")
expect(ok.status).to_equal("completed")
expect(ok.kind).to_equal("playback-period")
expect(ok.sequence).to_equal(7u64)
expect(virtio_snd_completion(8u64, 0, 4u64, 3u64, 480, "capture").status).to_equal("stale-generation")
expect(virtio_snd_completion(9u64, 0, 4u64, 4u64, -1, "capture").status).to_equal("malformed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple VirtIO sound protocol.
- pure-Simple VirtIO sound protocol

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

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b3497c533bd577430e57291a4f4c7b130a167eb60de0ea511cc9b63d4f94432`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b3497c533bd577430e57291a4f4c7b130a167eb60de0ea511cc9b63d4f94432`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b3497c533bd577430e57291a4f4c7b130a167eb60de0ea511cc9b63d4f94432`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes exact little-endian control request layouts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps device status without accepting unknown values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes jack period and xrun event payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
