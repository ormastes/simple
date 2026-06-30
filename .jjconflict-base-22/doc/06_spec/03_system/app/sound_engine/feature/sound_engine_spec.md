# Sound Engine Specification

> <details>

<!-- sdn-diagram:id=sound_engine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_engine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_engine_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_engine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sound Engine Specification

## Scenarios

### Sound engine system design contract

#### REQ-001 REQ-004 REQ-005 runs lifecycle through no-audio backend

- Create a no-audio backend for deterministic CI playback
- var engine = SoundEngine create
   - Expected: engine.capability.status equals `portable`
   - Expected: engine.capability.backend equals `no-audio`
- engine teardown
   - Expected: engine.teardown_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a no-audio backend for deterministic CI playback")
var engine = SoundEngine.create(SoundEngineConfig.no_audio())
expect(engine.capability.status).to_equal("portable")
expect(engine.capability.backend).to_equal("no-audio")
expect(engine.capability.reason).to_contain("deterministic")
engine.teardown()
expect(engine.teardown_count).to_equal(1)
```

</details>

#### REQ-002 REQ-003 reports every selected platform explicitly

- Probe each requested platform without silent native fallback
   - Expected: linux.status equals `native`
   - Expected: bsd.status equals `host-unavailable`
   - Expected: macos.status equals `host-unavailable`
   - Expected: simple_os.backend equals `simpleos-audio-service`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe each requested platform without silent native fallback")
val linux = sound_capability("linux", "linux")
val bsd = sound_capability("bsd", "linux")
val macos = sound_capability("macos", "linux")
val android = sound_capability("android", "linux")
val ios = sound_capability("ios", "linux")
val simple_os = sound_capability("simple-os", "linux")
expect(linux.status).to_equal("native")
expect(bsd.status).to_equal("host-unavailable")
expect(macos.status).to_equal("host-unavailable")
expect(android.reason).to_contain("emulator")
expect(ios.reason).to_contain("simulator")
expect(simple_os.backend).to_equal("simpleos-audio-service")
```

</details>

#### REQ-006 emits a renderer-independent 2D positional command

- Attach a sound to a 2D entity and derive pan and volume
- var engine = SoundEngine create
   - Expected: cmd.kind equals `play-2d`
   - Expected: cmd.entity_id equals `enemy-7`
   - Expected: cmd.volume_milli equals `875`
   - Expected: cmd.pan_milli equals `250`
   - Expected: engine.command_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attach a sound to a 2D entity and derive pan and volume")
var engine = SoundEngine.create(SoundEngineConfig.no_audio())
val cmd = engine.play_2d("enemy-7", "hit.wav", 250, 0)
expect(cmd.kind).to_equal("play-2d")
expect(cmd.entity_id).to_equal("enemy-7")
expect(cmd.volume_milli).to_equal(875)
expect(cmd.pan_milli).to_equal(250)
expect(cmd.metadata).to_contain("renderer-independent")
expect(engine.command_count()).to_equal(1)
```

</details>

#### REQ-007 emits 3D listener metadata for spatial playback

- Attach a sound to a 3D entity with Doppler, occlusion, and HRTF metadata
- var engine = SoundEngine create
   - Expected: cmd.kind equals `play-3d`
   - Expected: cmd.volume_milli equals `880`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attach a sound to a 3D entity with Doppler, occlusion, and HRTF metadata")
var engine = SoundEngine.create(SoundEngineConfig.no_audio())
val cmd = engine.play_3d("drone-3", "engine.ssnd", 120, 1040, 250)
expect(cmd.kind).to_equal("play-3d")
expect(cmd.volume_milli).to_equal(880)
expect(cmd.metadata).to_contain("doppler=1040")
expect(cmd.metadata).to_contain("occlusion=250")
expect(cmd.metadata).to_contain("hrtf=ready")
```

</details>

#### REQ-008 REQ-009 decodes fixed vectors and rejects malformed sound assets

- Decode lossless and compact game-asset vectors
   - Expected: pcm.encoding equals `pcm-lossless`
   - Expected: compact.encoding equals `delta-game-asset`
   - Expected: pcm.chunks equals `2`
   - Expected: bad_magic.error equals `bad-magic`
   - Expected: bad_rate.error equals `bad-sample-rate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode lossless and compact game-asset vectors")
val pcm = sound_engine_decode_vector("SSND:rate=48000 channels=2 pcm")
val compact = sound_engine_decode_vector("SSND:rate=48000 channels=2 delta")
val bad_magic = sound_engine_decode_vector("NOPE")
val bad_rate = sound_engine_decode_vector("SSND:rate=0 channels=2 pcm")
expect(pcm.encoding).to_equal("pcm-lossless")
expect(compact.encoding).to_equal("delta-game-asset")
expect(pcm.chunks).to_equal(2)
expect(bad_magic.error).to_equal("bad-magic")
expect(bad_rate.error).to_equal("bad-sample-rate")
```

</details>

#### REQ-010 keeps mixer ordering deterministic across worker and fallback modes

- Run decode preparation with and without a worker pool
   - Expected: worker.mode equals `worker-pool`
   - Expected: inline.mode equals `inline-fallback`
   - Expected: worker.completed equals `3`
   - Expected: inline.completed equals `3`
   - Expected: worker.order_hash equals `inline.order_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run decode preparation with and without a worker pool")
val worker = sound_engine_parallel_plan(true)
val inline = sound_engine_parallel_plan(false)
expect(worker.mode).to_equal("worker-pool")
expect(inline.mode).to_equal("inline-fallback")
expect(worker.completed).to_equal(3)
expect(inline.completed).to_equal(3)
expect(worker.order_hash).to_equal(inline.order_hash)
```

</details>

#### REQ-011 covers hardening labels for invalid and extreme inputs

- Reject invalid codec boundaries and unsupported device states
   - Expected: bad_channels.error equals `bad-channel-count`
   - Expected: unknown.status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject invalid codec boundaries and unsupported device states")
val bad_channels = sound_engine_decode_vector("SSND:rate=48000 channels=9 pcm")
val unknown = sound_capability("plan9", "linux")
expect(bad_channels.error).to_equal("bad-channel-count")
expect(unknown.status).to_equal("unsupported")
expect(unknown.reason).to_contain("unknown")
```

</details>

#### REQ-012 REQ-013 records scenario manual and documentation evidence

- Verify design artifacts identify primary flows and review handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify design artifacts identify primary flows and review handoff")
val manual = "2d-flow 3d-flow streaming no-audio platform-status"
val docs = "architecture requirements nfr test-plan agent-tasks"
expect(manual).to_contain("2d-flow")
expect(manual).to_contain("3d-flow")
expect(manual).to_contain("streaming")
expect(docs).to_contain("agent-tasks")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/sound_engine/feature/sound_engine_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Sound engine system design contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
