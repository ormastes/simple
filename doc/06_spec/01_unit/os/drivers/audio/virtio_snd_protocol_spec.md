# virtio_snd_protocol_spec

> Verifies the virtio snd protocol behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# virtio_snd_protocol_spec

Verifies the virtio snd protocol behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the virtio snd protocol behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### pure-Simple VirtIO sound protocol

#### encodes exact little-endian control request layouts

- Verify: encodes exact little-endian control request layouts
   - Expected: info.len() equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: info[0].to_i64() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: info[1].to_i64() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: params.len() equals `24)  # oracle: pinned constant asserted by this scenario`
   - Expected: params[20].to_i64() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: params[21].to_i64() equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: params[22].to_i64() equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: start.len() equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: encodes exact little-endian control request layouts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val info = virtio_snd_pcm_info_query(2u32, 3u32)
val params = virtio_snd_pcm_set_params([
    1u32, 4096u32, 1024u32, 2u32,
    VIRTIO_SND_PCM_FMT_S16.to_u32(), VIRTIO_SND_PCM_RATE_48000.to_u32()
])
val start = virtio_snd_pcm_command(VIRTIO_SND_R_PCM_START, 1u32)
expect(info.len()).to_equal(16)  # oracle: pinned constant asserted by this scenario
expect(info[0].to_i64()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(info[1].to_i64()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(params.len()).to_equal(24)  # oracle: pinned constant asserted by this scenario
expect(params[20].to_i64()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(params[21].to_i64()).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(params[22].to_i64()).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(start.len()).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

#### maps device status without accepting unknown values

- Verify: maps device status without accepting unknown values
   - Expected: virtio_snd_status_name(VIRTIO_SND_S_OK) equals `ok`
   - Expected: virtio_snd_status_name(VIRTIO_SND_S_NOT_SUPP) equals `unsupported`
   - Expected: virtio_snd_status_name(0xDEADu32) equals `unknown-status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: maps device status without accepting unknown values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(virtio_snd_status_name(VIRTIO_SND_S_OK)).to_equal("ok")
expect(virtio_snd_status_name(VIRTIO_SND_S_NOT_SUPP)).to_equal("unsupported")
expect(virtio_snd_status_name(0xDEADu32)).to_equal("unknown-status")
```

</details>

#### decodes jack period and xrun event payloads

- Verify: decodes jack period and xrun event payloads
   - Expected: jack.kind equals `audio-jack-connected`
   - Expected: jack.target_id equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: period.status equals `completed`
   - Expected: xrun.status equals `xrun`
   - Expected: virtio_snd_decode_event(0xFFFFu32, 0u32).status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: decodes jack period and xrun event payloads")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val jack = virtio_snd_decode_event(VIRTIO_SND_EVT_JACK_CONNECTED, 3u32)
val period = virtio_snd_decode_event(VIRTIO_SND_EVT_PCM_PERIOD_ELAPSED, 2u32)
val xrun = virtio_snd_decode_event(VIRTIO_SND_EVT_PCM_XRUN, 2u32)
expect(jack.kind).to_equal("audio-jack-connected")
expect(jack.target_id).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(period.status).to_equal("completed")
expect(xrun.status).to_equal("xrun")
expect(virtio_snd_decode_event(0xFFFFu32, 0u32).status).to_equal("unsupported")
```

</details>

#### negotiates bounded playback and capture capabilities

- Verify: negotiates bounded playback and capture capabilities
   - Expected: result.status equals `accepted`
   - Expected: result.playback is true
   - Expected: result.capture is true
   - Expected: result.accepted_features equals `VIRTIO_SND_F_PCM_INFO | VIRTIO_SND_F_CHMAP_INFO`
   - Expected: virtio_snd_negotiate(0u64, 0, 0).status equals `unsupported`
   - Expected: virtio_snd_negotiate(0u64, -1, 0).status equals `malformed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: negotiates bounded playback and capture capabilities")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: validates period and DMA bounds
   - Expected: valid.status equals `accepted`
   - Expected: valid.period_bytes equals `1920)  # oracle: pinned constant asserted by this scenario`
   - Expected: valid.buffer_bytes equals `7680)  # oracle: pinned constant asserted by this scenario`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: -1, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-stream`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "bad", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-direction`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 0, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status equals `invalid-format`
   - Expected: virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1000)).status equals `invalid-buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: validates period and DMA bounds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val valid = virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920))
expect(valid.status).to_equal("accepted")
expect(valid.period_bytes).to_equal(1920)  # oracle: pinned constant asserted by this scenario
expect(valid.buffer_bytes).to_equal(7680)  # oracle: pinned constant asserted by this scenario
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: -1, direction: "playback", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-stream")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "bad", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-direction")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 0, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1920)).status).to_equal("invalid-format")
expect(virtio_snd_validate_pcm(VirtioSndPcmRequest(stream_id: 0, direction: "capture", sample_rate: 48000, channels: 2, period_frames: 480, periods: 4, buffer_frames: 1000)).status).to_equal("invalid-buffer")
```

</details>

#### enforces stream lifecycle and generation invalidation

- Verify: enforces stream lifecycle and generation invalidation
   - Expected: prepared.next_state equals `prepared`
   - Expected: prepared.generation equals `4u64`
   - Expected: virtio_snd_stream_transition("prepared", "start", 4u64).next_state equals `running`
   - Expected: virtio_snd_stream_transition("running", "release", 4u64).status equals `invalid-state`
   - Expected: lost.status equals `disconnected`
   - Expected: lost.generation equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: enforces stream lifecycle and generation invalidation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects stale and malformed completions
   - Expected: ok.status equals `completed`
   - Expected: ok.kind equals `playback-period`
   - Expected: ok.sequence equals `7u64`
   - Expected: virtio_snd_completion(8u64, 0, 4u64, 3u64, 480, "capture").status equals `stale-generation`
   - Expected: virtio_snd_completion(9u64, 0, 4u64, 4u64, -1, "capture").status equals `malformed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003
step("Verify: rejects stale and malformed completions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = virtio_snd_completion(7u64, 0, 4u64, 4u64, 480, "playback")
expect(ok.status).to_equal("completed")
expect(ok.kind).to_equal("playback-period")
expect(ok.sequence).to_equal(7u64)
expect(virtio_snd_completion(8u64, 0, 4u64, 3u64, 480, "capture").status).to_equal("stale-generation")
expect(virtio_snd_completion(9u64, 0, 4u64, 4u64, -1, "capture").status).to_equal("malformed")
```

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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d7893667864f12825227d59abf4dfb01e6af3d012126d94520a2bc1ab8bcc8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d7893667864f12825227d59abf4dfb01e6af3d012126d94520a2bc1ab8bcc8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d7893667864f12825227d59abf4dfb01e6af3d012126d94520a2bc1ab8bcc8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/drivers/audio/virtio_snd_protocol_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
