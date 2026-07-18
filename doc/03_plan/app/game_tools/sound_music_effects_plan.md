# Plan: Minimal Sound/Music/Effect Authoring Toolset

Scope is deliberately small: an SDN sound-description format + a `simple sound` CLI that
renders it to a byte-identical WAV, reusing the existing engine/effects code. No GUI, no
tracker, no capture — see the research doc's YAGNI list. Order below is the build order; each
step is independently usable and testable.

## Step 1 — WAV encoder, pure Simple (the actual gap)
- New file `src/lib/common/audio/wav_encode.spl` — a WAV (RIFF/PCM16 + float32) encoder is
  header bytes + interleaved samples; pure Simple, no runtime change. [fable review: the
  original draft put this in `src/runtime/runtime_audio.c` via miniaudio `ma_encoder`; that
  violates the pure-Simple-first rule and is unnecessary — WAV is trivially encodable in
  Simple, and the netcode lane's `ByteWriter` (or plain byte building) covers it.]
- Write via the existing `std.io_runtime.file_write` facade; no new externs.
- Oracle: encode a known sample buffer (e.g. `[0.0, 0.5, -0.5, 1.0]`), assert exact header
  bytes (RIFF/fmt/data chunk fields) AND exact sample bytes at known offsets; round-trip
  through the existing decode path where available — not "plays without crashing."

## Step 2 — Minimal sound-shape primitives (envelope + tone/noise, pure Simple)
- New file `src/lib/common/engine/audio/sound_synth.spl` (pure, FFI-free, sits next to
  `sound_contract.spl`): a linear ADSR envelope over a sample buffer (`apply_adsr(samples,
  attack_ms, decay_ms, sustain_level, release_ms, sample_rate) -> [f64]`) and two generators
  (`gen_sine(freq_hz, duration_ms, sample_rate) -> [f64]`, `gen_white_noise(duration_ms,
  sample_rate, seed) -> [f64]` — seeded PRNG for determinism, no OS entropy).
- Deliberately excluded: multi-oscillator synthesis, FM/wavetable, filters (reuse
  `EffectsChain`/miniaudio node graph for that instead of reimplementing DSP in Simple).
- Layering (footstep + pitch jitter, etc.) is just "call `gen_*`/`apply_adsr` N times and mix
  buffers" at the CLI/SDN level — no new abstraction needed.

## Step 3 — SDN sound/music description format
- Reuse `src/lib/common/sdn/{parser,value,document}.spl` (already used by
  `src/lib/nogc_sync_mut/game2d/config/game_sdn.spl` — follow that file's load pattern:
  `parse_with_spans` → typed config class with `static fn default()` and a loader that reports
  `AssetError` on bad shape).
- New loader: `src/lib/nogc_sync_mut/game2d/audio/sound_asset_sdn.spl` (mirrors
  `game_sdn.spl`'s structure). Minimal shape:
  ```
  sound:
    kind: "sfx" | "sequence"     # "sequence" = flat event list, NOT a tracker
    source: { type: "tone", freq_hz: 440, duration_ms: 200 }   # or type: "file", path: "..."
    envelope: { attack_ms: 5, decay_ms: 50, sustain: 0.6, release_ms: 100 }
    effects: [ { type: "lowpass", cutoff_hz: 800 }, ... ]   # maps directly onto effects.spl's AudioEffect
    events: [ { at_ms: 0, clip: "kick.wav", gain: 1.0 }, { at_ms: 250, clip: "snare.wav" } ]  # sequence only
  ```
- `events` is the "simple music sequencing" ask — a flat, timestamped clip-trigger list, not
  note/pattern/instrument tracker semantics. If a real game later needs note-level sequencing,
  that's a new, separately-justified feature, not a default-scope item here.

## Step 4 — `simple sound` CLI subcommand
- Register in `src/app/cli/dispatch/table.spl` next to `"lint"`/`"fmt"`/`"check"` (~line 114–142).
- New `src/app/cli/sound_cmd.spl` with three subcommands, each a thin composition of steps 1–3:
  - `simple sound validate <file.sdn>` — parse + type-check only, exit code + error text.
  - `simple sound render <file.sdn> -o out.wav` — build the sample buffer (steps 2/3), apply
    `EffectsChain` where feasible in pure Simple (one-pole low/high-pass, delay, and offline
    Schroeder reverb — 4 parallel comb + 2 series allpass, `sound_synth.reverb` — are a few
    lines each; reuse `effects.spl`'s data model). HRTF stays deferred — if it's ever needed,
    record the `runtime_need` decision first per the SPipe runtime-boundary rule rather than
    defaulting to a `runtime_audio.c` sink. Encode via step 1. Must be byte-deterministic given
    the same SDN input (no wall-clock/random seeds unless an explicit `seed:` field is set).
  - `simple sound play <file.sdn>` — render to a temp WAV, then `audio_play` via the existing
    `AudioManager`/`audio_sffi.spl` path. Manual/local use only, not asserted in CI.
- Explicitly not building: a TUI waveform view, live parameter tweaking, undo/redo. If
  `validate`/`render`/`play` prove insufficient, extend the CLI — don't pre-build an editor
  shell for a workflow that doesn't exist yet.

## Top 3 items (priority order)
1. **WAV encoder extern + Simple wrapper** (Step 1) — unblocks every downstream oracle; without
   it nothing here can be tested deterministically.
2. **SDN sound format + `simple sound render`** (Steps 3–4, render only) — the actual authoring
   loop: describe once, get a reproducible file.
3. **Envelope/tone-gen primitives + effects-chain wiring into render** (Step 2, plus the effects
   half of Step 4) — makes `render` produce something more than a flat tone or raw file copy.

`validate`/`play` subcommands and the `events`/sequence shape are lower priority — real, but
buildable after 1–3 land and prove the loop out.

## BDD plan (SSpec, absolute oracles only — never play-and-hope)

New spec files, following the existing `describe "..." / it "..."` style seen in
`test/01_unit/lib/engine/audio_bus_spec.spl`:

- `test/01_unit/lib/common/audio_synth/sound_synth_spec.spl`
  - `describe "gen_sine"`
    - `it "produces exact sample values for a 1kHz tone at 8kHz sample rate"` — assert
      `gen_sine(1000.0, 1.0, 8000)[0..4]` equals precomputed `sin(2*pi*f*t)` values to a fixed
      tolerance (e.g. 1e-9), not just "length > 0" or "not silent."
    - `it "returns a buffer of exactly duration_ms * sample_rate / 1000 frames"`
  - `describe "gen_white_noise"`
    - `it "is deterministic for a given seed — two calls with the same seed produce identical buffers"`
    - `it "produces different buffers for different seeds"`
  - `describe "apply_adsr"`
    - `it "zeroes the first sample when attack_ms > 0"`
    - `it "reaches sustain_level exactly at attack_ms + decay_ms"` — assert the exact sample
      index and its value, e.g. `envelope[attack_frames + decay_frames] == sustain_level` within
      float epsilon.
    - `it "decays to zero by the end of release_ms"` — assert last sample `== 0.0` (or within
      epsilon), not "quieter than before."

- `test/01_unit/lib/nogc_sync_mut/game2d/audio/sound_asset_sdn_spec.spl`
  - `describe "sound_asset_sdn load"`
    - `it "parses a minimal tone sound.sdn into freq_hz=440, duration_ms=200"` — assert the
      typed struct fields directly.
    - `it "rejects a sound.sdn missing the required source.type field with AssetError"`
    - `it "parses a sequence kind with 2 events at exact at_ms offsets"`

- `test/01_unit/app/cli/sound_cmd_render_spec.spl`
  - `describe "simple sound render"`
    - `it "renders a fixed tone SDN to a WAV whose sample bytes at offset 44 (post RIFF header)
      through offset 52 exactly match a precomputed reference buffer"` — read the rendered file
      back with a raw byte read (or the step-1 decode wrapper) and assert specific offsets/values,
      not "file exists" or "file size > 0."
    - `it "produces byte-identical WAV output across two separate render invocations of the
      same SDN input"` — hash-compare (or full byte-compare) two renders; this is the
      determinism oracle that rules out any hidden wall-clock/RNG dependency.
    - `it "applies a lowpass effect entry such that high-frequency energy in the rendered
      buffer is measurably reduced versus an unfiltered render of the same tone"` — compare
      specific sample-magnitude deltas between two renders (with/without the effect), still a
      concrete numeric assertion, not a subjective "sounds filtered."
    - `it "exits non-zero with a parse error message when given a malformed SDN file"`

No test in this plan renders and plays back through a live audio device for assertion — the
`play` subcommand stays manual/local-only, consistent with `.claude/rules/testing.md` and the
existing project pattern (`audio_ffi_spec.spl` tests the SFFI surface, not sound-alike output).
