# Sound Engine Contract Specification

> <details>

<!-- sdn-diagram:id=sound_engine_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_engine_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_engine_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_engine_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sound Engine Contract Specification

## Scenarios

### Sound engine contract

#### maps known backend statuses

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = sound_capability("linux", "linux")
val simple_os = sound_capability("simple-os", "linux")
val unknown = sound_capability("unknown-os", "linux")
expect(linux.status).to_equal("native")
expect(simple_os.status).to_equal("portable")
expect(unknown.status).to_equal("unsupported")
expect(sound_backend_status_valid("native")).to_be(true)
expect(sound_backend_status_valid("host-unavailable")).to_be(true)
expect(sound_backend_status_valid("maybe")).to_be(false)
```

</details>

#### creates deterministic no-audio engine and clears commands on teardown

- var engine = SoundEngine create
   - Expected: engine.capability.backend equals `no-audio`
   - Expected: first.pan_milli equals `500`
   - Expected: engine.command_count() equals `2`
- engine teardown
   - Expected: engine.command_count() equals `0`
   - Expected: engine.teardown_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = SoundEngine.create(SoundEngineConfig.no_audio())
val first = engine.play_2d("node-a", "hit.wav", 500, 0)
val second = engine.play_3d("node-b", "wind.ssnd", 100, 1000, 0)
expect(engine.capability.backend).to_equal("no-audio")
expect(first.pan_milli).to_equal(500)
expect(second.metadata).to_contain("hrtf=ready")
expect(engine.command_count()).to_equal(2)
engine.teardown()
expect(engine.command_count()).to_equal(0)
expect(engine.teardown_count).to_equal(1)
```

</details>

#### clamps 2D pan and 3D volume

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = sound_command_2d("node", "clip", -2500, 0)
val far = sound_command_3d("node", "clip", 5000, 1000, 0)
expect(left.pan_milli).to_equal(-1000)
expect(left.volume_milli).to_equal(500)
expect(far.volume_milli).to_equal(0)
```

</details>

#### decodes design vectors and rejects malformed headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pcm = sound_decode_design_vector("SSND:rate=48000 channels=2 pcm")
val delta = sound_decode_design_vector("SSND:rate=48000 channels=2 delta")
val bad_magic = sound_decode_design_vector("BAD")
val bad_channels = sound_decode_design_vector("SSND:rate=48000 channels=0 pcm")
expect(pcm.encoding).to_equal("pcm-lossless")
expect(delta.encoding).to_equal("delta-game-asset")
expect(bad_magic.error).to_equal("bad-magic")
expect(bad_channels.error).to_equal("bad-channel-count")
```

</details>

#### records worker pool versus inline fallback evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val worker = sound_parallel_plan(true)
val inline = sound_parallel_plan(false)
expect(worker.mode).to_equal("worker-pool")
expect(inline.mode).to_equal("inline-fallback")
expect(worker.order_hash).to_equal(inline.order_hash)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/sound_engine_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Sound engine contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
