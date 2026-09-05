# sound CLI pattern (tracker-LITE step sequencing)

> `sound.kind: "pattern"` is a step-sequencer front end over the existing `"sequence"` flat event list — a pure lowering, no new mixing code. Each `pattern.tracks[].steps` string is one character per step: `x` triggers the track's clip at gain 0.7, `X` triggers it accented at gain 1.0, `.` rests. Step duration is `60000 / bpm / steps_per_beat` ms; step `i` of repeat `r` fires at `(r * steps.len() + i) * step_ms`. All tracks must share one `steps` length. `simple sound render` lowers a pattern to `events` and renders it through the unchanged sequence mixer.

<!-- sdn-diagram:id=sound_cmd_pattern_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_cmd_pattern_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_cmd_pattern_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_cmd_pattern_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sound CLI pattern (tracker-LITE step sequencing)

`sound.kind: "pattern"` is a step-sequencer front end over the existing `"sequence"` flat event list — a pure lowering, no new mixing code. Each `pattern.tracks[].steps` string is one character per step: `x` triggers the track's clip at gain 0.7, `X` triggers it accented at gain 1.0, `.` rests. Step duration is `60000 / bpm / steps_per_beat` ms; step `i` of repeat `r` fires at `(r * steps.len() + i) * step_ms`. All tracks must share one `steps` length. `simple sound render` lowers a pattern to `events` and renders it through the unchanged sequence mixer.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #sound-cmd-pattern |
| Category | App / CLI Surface |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_tools/sound_music_effects_plan.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/cli/sound_cmd_pattern_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`sound.kind: "pattern"` is a step-sequencer front end over the existing
`"sequence"` flat event list — a pure lowering, no new mixing code. Each
`pattern.tracks[].steps` string is one character per step: `x` triggers the
track's clip at gain 0.7, `X` triggers it accented at gain 1.0, `.` rests.
Step duration is `60000 / bpm / steps_per_beat` ms; step `i` of repeat `r`
fires at `(r * steps.len() + i) * step_ms`. All tracks must share one
`steps` length. `simple sound render` lowers a pattern to `events` and
renders it through the unchanged sequence mixer.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Pattern SDN | `sound.pattern: { bpm, steps_per_beat, repeat, tracks: [{clip, steps}] }` |
| Step chars | `x` = trigger (gain 0.7), `X` = accent (gain 1.0), `.` = rest |
| Step duration | `60000 / bpm / steps_per_beat` ms, truncated to whole ms when applied |
| Repeat | Pattern replayed `repeat` times, each repeat offset by the full pattern length |
| Validation | `bpm > 0`, `steps_per_beat > 0`, `repeat >= 1`, equal-length `steps` across tracks, referenced clips must exist |
| Exit codes | 0 success, 1 failure (bad pattern shape, missing clip), 2 usage error |

## Syntax

```
sound:
  kind: "pattern"
  sample_rate: 22050
  pattern:
    bpm: 120
    steps_per_beat: 4
    repeat: 2
    tracks:
      - { clip: "kick.sdn", steps: "x...x...x...x..." }
      - { clip: "hat.wav",  steps: "..x...x...x...x." }
```

## Examples

```
simple sound render pattern.sdn -o pattern.wav
wrote pattern.wav (1796 bytes, 1000 Hz)
```

**Requirements:** N/A
**Plan:** doc/03_plan/app/game_tools/sound_music_effects_plan.md
**Design:** N/A
**Research:** N/A

## Scenarios

### simple sound render (pattern)

#### 120bpm/4 steps-per-beat gives an exact 125ms step duration (single hit at step index 1 lands on frame 125, not 124/126)

- Write a 2-step pattern \
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \".X\" } ]\n") is true
- Render and decode; the hit must land exactly at frame 125 (125ms @ 1000Hz)
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a 2-step pattern \".X\" — the only (accented) hit is step index 1")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/step_duration.sdn"
expect(_write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \".X\" } ]\n")).to_equal(true)

step("Render and decode; the hit must land exactly at frame 125 (125ms @ 1000Hz)")
val out = OUT_DIR + "/step_duration.wav"
val r = run_cli("render " + sdn + " -o " + out)
var samples: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out)):
    samples = a.samples
val ok = (r.exit_code == 0 and samples.len() == 126 and samples[124] == 0.0 and samples[125] == 0.5)
expect(ok).to_equal(true)
```

</details>

#### steps \

- Write a 4-step pattern \
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n") is true
- Render and decode; hits at frame 0 and frame 375, both at gain 0.7 (0.5 * 0.7 quantized)
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a 4-step pattern \"x..x\" (hits at step 0 and step 3)")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/xdotdotx.sdn"
expect(_write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n")).to_equal(true)

step("Render and decode; hits at frame 0 and frame 375, both at gain 0.7 (0.5 * 0.7 quantized)")
val out = OUT_DIR + "/xdotdotx.wav"
val r = run_cli("render " + sdn + " -o " + out)
var samples: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out)):
    samples = a.samples
val ok = (r.exit_code == 0 and samples.len() == 376 and
    samples[0] == 0.34997558593750 and samples[375] == 0.34997558593750)
expect(ok).to_equal(true)
```

</details>

#### accent 'X' lowers to gain 1.0 versus 'x' gain 0.7 — exact quantized amplitudes

- Render single-step patterns \
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn_x, "    tracks: [ { clip: \"click.wav\", steps: \"x\" } ]\n") is true
   - Expected: _write_sdn(sdn_upper_x, "    tracks: [ { clip: \"click.wav\", steps: \"X\" } ]\n") is true
- Render both; decode sample[0] of each
- Then 'x' quantizes to 0.5*0.7 and 'X' quantizes to 0.5*1.0 exactly
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render single-step patterns \"x\" and \"X\" from the same 0.5-amplitude clip")
expect(_write_clips()).to_equal(true)
val sdn_x = OUT_DIR + "/accent_x.sdn"
val sdn_upper_x = OUT_DIR + "/accent_upper_x.sdn"
expect(_write_sdn(sdn_x, "    tracks: [ { clip: \"click.wav\", steps: \"x\" } ]\n")).to_equal(true)
expect(_write_sdn(sdn_upper_x, "    tracks: [ { clip: \"click.wav\", steps: \"X\" } ]\n")).to_equal(true)

step("Render both; decode sample[0] of each")
val out_x = OUT_DIR + "/accent_x.wav"
val out_upper_x = OUT_DIR + "/accent_upper_x.wav"
val rx = run_cli("render " + sdn_x + " -o " + out_x)
val rX = run_cli("render " + sdn_upper_x + " -o " + out_upper_x)
var samples_x: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out_x)):
    samples_x = a.samples
var samples_upper_x: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out_upper_x)):
    samples_upper_x = a.samples

step("Then 'x' quantizes to 0.5*0.7 and 'X' quantizes to 0.5*1.0 exactly")
val ok = (rx.exit_code == 0 and rX.exit_code == 0 and
    samples_x[0] == 0.34997558593750 and samples_upper_x[0] == 0.5)
expect(ok).to_equal(true)
```

</details>

#### repeat:2 duplicates the pattern's events offset by exactly the pattern length (4 steps * 125ms = 500ms)

- Write the same \
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    repeat: 2\n    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n") is true
- Render and decode; hits at frames 0, 375 (repeat 0) and 500, 875 (repeat 1)
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the same \"x..x\" pattern with repeat: 2")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/repeat2.sdn"
expect(_write_sdn(sdn, "    repeat: 2\n    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n")).to_equal(true)

step("Render and decode; hits at frames 0, 375 (repeat 0) and 500, 875 (repeat 1)")
val out = OUT_DIR + "/repeat2.wav"
val r = run_cli("render " + sdn + " -o " + out)
var samples: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out)):
    samples = a.samples
val ok = (r.exit_code == 0 and samples.len() == 876 and
    samples[0] == 0.34997558593750 and samples[375] == 0.34997558593750 and
    samples[500] == 0.34997558593750 and samples[875] == 0.34997558593750)
expect(ok).to_equal(true)
```

</details>

#### two tracks triggering the same step mix to the exact summed sample

- Write a 1-step pattern where both tracks (click 0.5, hat 0.25) hit accented on step 0
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"X\" }, { clip: \"hat.wav\", steps: \"X\" } ]\n") is true
- Render and decode; the single frame is exactly click(0.5) + hat(0.25) = 0.75
- run cli
   - Expected: samples[0] equals `0.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a 1-step pattern where both tracks (click 0.5, hat 0.25) hit accented on step 0")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/collide.sdn"
expect(_write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"X\" }, { clip: \"hat.wav\", steps: \"X\" } ]\n")).to_equal(true)

step("Render and decode; the single frame is exactly click(0.5) + hat(0.25) = 0.75")
val out = OUT_DIR + "/collide.wav"
run_cli("render " + sdn + " -o " + out)
var samples: [f32] = []
if val Ok(a) = decode_wav(file_read_bytes(out)):
    samples = a.samples
expect(samples[0]).to_equal(0.75)
```

</details>

#### produces byte-identical WAV output across two separate pattern render invocations

- Render the same pattern SDN twice to two separate files
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    repeat: 2\n    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n") is true
- Then both files hash identically
- file hash sha256
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same pattern SDN twice to two separate files")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/det.sdn"
expect(_write_sdn(sdn, "    repeat: 2\n    tracks: [ { clip: \"click.wav\", steps: \"x..x\" } ]\n")).to_equal(true)
val out_a = OUT_DIR + "/det_a.wav"
val out_b = OUT_DIR + "/det_b.wav"
val ra = run_cli("render " + sdn + " -o " + out_a)
val rb = run_cli("render " + sdn + " -o " + out_b)

step("Then both files hash identically")
val ok = (ra.exit_code == 0 and rb.exit_code == 0 and
    file_hash_sha256(out_a) == file_hash_sha256(out_b))
expect(ok).to_equal(true)
```

</details>

#### exits 1 when tracks have mismatched step-string lengths

- Write a pattern where track 0 has 4 steps and track 1 has 3
   - Expected: _write_clips() is true
   - Expected: _write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"x..x\" }, { clip: \"hat.wav\", steps: \"x..\" } ]\n") is true
- Then render fails (exit 1) naming the length mismatch
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a pattern where track 0 has 4 steps and track 1 has 3")
expect(_write_clips()).to_equal(true)
val sdn = OUT_DIR + "/mismatch.sdn"
expect(_write_sdn(sdn, "    tracks: [ { clip: \"click.wav\", steps: \"x..x\" }, { clip: \"hat.wav\", steps: \"x..\" } ]\n")).to_equal(true)

step("Then render fails (exit 1) naming the length mismatch")
val r = run_cli("render " + sdn + " -o " + OUT_DIR + "/mismatch_never.wav")
val ok = (r.exit_code == 1 and r.stdout.contains("does not match"))
expect(ok).to_equal(true)
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


## Related Documentation

- **Plan:** [doc/03_plan/app/game_tools/sound_music_effects_plan.md](doc/03_plan/app/game_tools/sound_music_effects_plan.md)


</details>
