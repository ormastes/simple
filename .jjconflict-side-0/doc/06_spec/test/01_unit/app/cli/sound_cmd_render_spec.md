# sound CLI render

> `simple sound render <file.sdn> -o out.wav` synthesizes a tone (kind `sfx`) or mixes a clip-trigger timeline (kind `sequence`) from an SDN sound description, and encodes it to a byte-deterministic 16-bit PCM WAV. `validate` type-checks only; `render` is the authoring loop under test here.

<!-- sdn-diagram:id=sound_cmd_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_cmd_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_cmd_render_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_cmd_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sound CLI render

`simple sound render <file.sdn> -o out.wav` synthesizes a tone (kind `sfx`) or mixes a clip-trigger timeline (kind `sequence`) from an SDN sound description, and encodes it to a byte-deterministic 16-bit PCM WAV. `validate` type-checks only; `render` is the authoring loop under test here.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #sound-cmd-render |
| Category | App / CLI Surface |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_tools/sound_music_effects_plan.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/cli/sound_cmd_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`simple sound render <file.sdn> -o out.wav` synthesizes a tone (kind `sfx`) or
mixes a clip-trigger timeline (kind `sequence`) from an SDN sound description,
and encodes it to a byte-deterministic 16-bit PCM WAV. `validate` type-checks
only; `render` is the authoring loop under test here.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Sound SDN | `sound:` block with `kind`, `sample_rate`, `source`, `envelope`, `effects` (`sfx`) or `events` (`sequence`) |
| Exit codes | 0 success, 1 failure (bad/missing sound, missing clip, unsupported render shape), 2 usage error |
| Sample oracle | PCM16 bytes at offset 44+ match trunc(sin(...)*32768) exactly |
| Determinism | Two renders of the same SDN are byte-identical |
| Sequence clips | `events[].clip` resolves next to the .sdn file — `.wav` (decoded) or `.sdn` (rendered recursively) — mixed at `at_ms` with `gain` |

## Syntax

```
simple sound validate <file.sdn>
simple sound render <file.sdn> -o out.wav
```

## Examples

```
simple sound render mysfx.sdn -o mysfx.wav
wrote mysfx.wav (60 bytes, 8000 Hz)
```

**Requirements:** N/A
**Plan:** doc/03_plan/app/game_tools/sound_music_effects_plan.md
**Design:** N/A
**Research:** N/A

## Scenarios

### simple sound render

#### renders a fixed 1kHz tone SDN to a WAV whose PCM16 sample bytes exactly match the precomputed reference

- Write the fixture SDN describing an 8kHz, 1ms, 1kHz sine tone
   - Expected: _write_fixtures() is true
- Render it to a WAV
   - Expected: r.exit_code equals `0`
- Then the header + first two sample bytes match the encoder's documented rounding
   - Expected: bytes.len() equals `60`
   - Expected: bytes[44] equals `0u8`
   - Expected: bytes[45] equals `0u8`
   - Expected: bytes[48] equals `255u8`
   - Expected: bytes[49] equals `127u8`
   - Expected: bytes[56] equals `0u8`
   - Expected: bytes[57] equals `128u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the fixture SDN describing an 8kHz, 1ms, 1kHz sine tone")
expect(_write_fixtures()).to_equal(true)

step("Render it to a WAV")
val out = OUT_DIR + "/tone.wav"
val r = run_cli("render " + TONE_SDN + " -o " + out)
expect(r.exit_code).to_equal(0)
expect(r.stdout).to_contain("wrote " + out)

step("Then the header + first two sample bytes match the encoder's documented rounding")
val bytes = file_read_bytes(out)
# 44-byte RIFF/fmt/data header + 8 samples * 2 bytes = 60
expect(bytes.len()).to_equal(60)
# sample[0] = sin(0) = 0.0 -> 0x0000
expect(bytes[44]).to_equal(0u8)
expect(bytes[45]).to_equal(0u8)
# sample[2] = sin(pi/2) = 1.0 -> clamped 32767 = 0x7FFF LE
expect(bytes[48]).to_equal(255u8)
expect(bytes[49]).to_equal(127u8)
# sample[6] = sin(3pi/2) = -1.0 -> -32768 = 0x8000 LE
expect(bytes[56]).to_equal(0u8)
expect(bytes[57]).to_equal(128u8)
```

</details>

#### produces byte-identical WAV output across two separate render invocations

- Render the same SDN twice to two separate files
   - Expected: _write_fixtures() is true
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then both files hash identically
   - Expected: ha equals `hb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same SDN twice to two separate files")
expect(_write_fixtures()).to_equal(true)
val out_a = OUT_DIR + "/det_a.wav"
val out_b = OUT_DIR + "/det_b.wav"
val ra = run_cli("render " + TONE_SDN + " -o " + out_a)
val rb = run_cli("render " + TONE_SDN + " -o " + out_b)
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then both files hash identically")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
expect(ha.len()).to_be_greater_than(0)
expect(ha).to_equal(hb)
```

</details>

#### applies a lowpass effect such that high-frequency sample magnitude is reduced versus an unfiltered render

- Render the same tone with and without a lowpass effect
   - Expected: _write_fixtures() is true
   - Expected: rp.exit_code equals `0`
   - Expected: rf.exit_code equals `0`
- Then the filtered peak sample (index 2) has strictly smaller magnitude


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same tone with and without a lowpass effect")
expect(_write_fixtures()).to_equal(true)
val plain_out = OUT_DIR + "/plain.wav"
val filtered_out = OUT_DIR + "/filtered.wav"
val rp = run_cli("render " + TONE_SDN + " -o " + plain_out)
val rf = run_cli("render " + LOWPASS_SDN + " -o " + filtered_out)
expect(rp.exit_code).to_equal(0)
expect(rf.exit_code).to_equal(0)

step("Then the filtered peak sample (index 2) has strictly smaller magnitude")
val plain_bytes = file_read_bytes(plain_out)
val filtered_bytes = file_read_bytes(filtered_out)
# sample[2] LE u16 at offset 48/49 — plain is clamped 32767 (peak, unfiltered)
val plain_peak_lo = plain_bytes[48] as i64
val plain_peak_hi = plain_bytes[49] as i64
val plain_peak = plain_peak_lo + plain_peak_hi * 256
val filtered_peak_lo = filtered_bytes[48] as i64
val filtered_peak_hi = filtered_bytes[49] as i64
val filtered_peak = filtered_peak_lo + filtered_peak_hi * 256
expect(filtered_peak).to_be_less_than(plain_peak)
```

</details>

#### produces byte-identical WAV output across two separate reverb render invocations

- Render the same reverb-effect SDN twice to two separate files
   - Expected: _write_fixtures() is true
- Then both files hash identically
- file hash sha256
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same reverb-effect SDN twice to two separate files")
expect(_write_fixtures()).to_equal(true)
val out_a = OUT_DIR + "/reverb_det_a.wav"
val out_b = OUT_DIR + "/reverb_det_b.wav"
val ra = run_cli("render " + REVERB_SDN + " -o " + out_a)
val rb = run_cli("render " + REVERB_SDN + " -o " + out_b)

step("Then both files hash identically")
val ok = (ra.exit_code == 0 and rb.exit_code == 0 and
    file_hash_sha256(out_a) == file_hash_sha256(out_b))
expect(ok).to_equal(true)
```

</details>

<details>
<summary>Advanced: exits 1 with a path-qualified error when a reverb effect's room_size is out of [0,1]</summary>

#### exits 1 with a path-qualified error when a reverb effect's room_size is out of [0,1]

- Render an SDN whose reverb effect has room_size=1.5
   - Expected: _write_fixtures() is true
- Then it fails (exit 1) and names the offending field
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render an SDN whose reverb effect has room_size=1.5")
expect(_write_fixtures()).to_equal(true)
val r = run_cli("render " + REVERB_BAD_SDN + " -o " + OUT_DIR + "/reverb_never.wav")

step("Then it fails (exit 1) and names the offending field")
val ok = (r.exit_code == 1 and r.stdout.contains("effects[0].room_size"))
expect(ok).to_equal(true)
```

</details>


</details>

#### exits non-zero with a parse error message when given a malformed SDN file

- Render a file that is not valid SDN
   - Expected: _write_fixtures() is true
   - Expected: r.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a file that is not valid SDN")
expect(_write_fixtures()).to_equal(true)
val r = run_cli("render " + BAD_SDN + " -o " + OUT_DIR + "/never.wav")
expect(r.exit_code).to_equal(1)
expect(r.stdout).to_contain("error:")
```

</details>

#### exits 2 when render is missing -o/--out

- Run render without an output path
   - Expected: _write_fixtures() is true
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run render without an output path")
expect(_write_fixtures()).to_equal(true)
val r = run_cli("render " + TONE_SDN)
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("missing -o/--out")
```

</details>

### simple sound render (sequence)

#### mixes 2 clip events onto the timeline sample-accurately with gain — clip A alone, then A+B overlap, then B alone

- Write kick.wav (0.5 x3 @1000Hz), snare.wav (0.25 x2 @1000Hz), and a sequence.sdn referencing both
   - Expected: _write_sequence_fixtures() is true
- Render the sequence: kick at_ms=0 gain=1.0, snare at_ms=2 gain=0.5
   - Expected: r.exit_code equals `0`
- Then the decoded samples are exactly [0.5, 0.5, kick[2]+0.5*snare[0]=0.625, 0.5*snare[1]=0.125]
   - Expected: samples equals `[0.5, 0.5, 0.625, 0.125]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write kick.wav (0.5 x3 @1000Hz), snare.wav (0.25 x2 @1000Hz), and a sequence.sdn referencing both")
expect(_write_sequence_fixtures()).to_equal(true)

step("Render the sequence: kick at_ms=0 gain=1.0, snare at_ms=2 gain=0.5")
val out = OUT_DIR + "/sequence.wav"
val r = run_cli("render " + SEQUENCE_SDN + " -o " + out)
expect(r.exit_code).to_equal(0)

step("Then the decoded samples are exactly [0.5, 0.5, kick[2]+0.5*snare[0]=0.625, 0.5*snare[1]=0.125]")
val decoded = decode_wav(file_read_bytes(out))
var samples: [f32] = []
if val Ok(a) = decoded:
    samples = a.samples
expect(samples).to_equal([0.5, 0.5, 0.625, 0.125])
```

</details>

#### produces byte-identical WAV output across two separate sequence render invocations

- Render the same sequence SDN twice to two separate files
   - Expected: _write_sequence_fixtures() is true
- Then both files hash identically
- file hash sha256
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same sequence SDN twice to two separate files")
expect(_write_sequence_fixtures()).to_equal(true)
val out_a = OUT_DIR + "/sequence_det_a.wav"
val out_b = OUT_DIR + "/sequence_det_b.wav"
val ra = run_cli("render " + SEQUENCE_SDN + " -o " + out_a)
val rb = run_cli("render " + SEQUENCE_SDN + " -o " + out_b)

step("Then both files hash identically")
val ok = (ra.exit_code == 0 and rb.exit_code == 0 and
    file_hash_sha256(out_a) == file_hash_sha256(out_b))
expect(ok).to_equal(true)
```

</details>

#### exits 1 with a path-qualified error when an event references a missing clip

- Render a sequence whose only event clip does not exist next to the SDN file
   - Expected: _write_sequence_fixtures() is true
- Then it fails (exit 1) and names the resolved clip path
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a sequence whose only event clip does not exist next to the SDN file")
expect(_write_sequence_fixtures()).to_equal(true)
val r = run_cli("render " + SEQUENCE_MISSING_SDN + " -o " + OUT_DIR + "/sequence_never.wav")

step("Then it fails (exit 1) and names the resolved clip path")
val ok = (r.exit_code == 1 and r.stdout.contains(OUT_DIR + "/does_not_exist.wav"))
expect(ok).to_equal(true)
```

</details>

### simple sound validate

#### prints an ok summary and exits 0 for a well-formed sound.sdn

- Validate the fixture SDN
   - Expected: _write_fixtures() is true
   - Expected: r.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate the fixture SDN")
expect(_write_fixtures()).to_equal(true)
val r = run_cli("validate " + TONE_SDN)
expect(r.exit_code).to_equal(0)
expect(r.stdout).to_contain("ok: " + TONE_SDN)
```

</details>

#### exits 1 with a clear error for a missing sound file

- Validate a path that does not exist
   - Expected: r.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate a path that does not exist")
val r = run_cli("validate " + OUT_DIR + "/there_is_no_such_file.sdn")
expect(r.exit_code).to_equal(1)
expect(r.stdout).to_contain("error: sound file not found")
```

</details>

### simple sound CLI usage errors

#### exits 2 with usage text when no subcommand is given

- Run the CLI with no arguments
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the CLI with no arguments")
val r = run_cli("")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("Usage: simple sound")
```

</details>

#### exits 2 on an unknown subcommand

- Run the CLI with a bogus subcommand
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the CLI with a bogus subcommand")
val r = run_cli("frobnicate")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("unknown subcommand: frobnicate")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_tools/sound_music_effects_plan.md](doc/03_plan/app/game_tools/sound_music_effects_plan.md)


</details>
