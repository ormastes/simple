# TL;DR — Sound/Music/Effect Tooling

**Runtime side (play+mix+spatialize) is solid. Authoring side (make new sounds/music) is empty.**

- `AudioManager` + `BusGraph`/`AudioGroupTree` + `MixerSnapshotManager` + doppler/occlusion:
  real, tested (30+7+10+6+5 `it` blocks), wired to miniaudio via `audio_sffi.spl`.
- `effects.spl` (LowPass/HighPass/Reverb/Delay) is a data model; the actual DSP runs in
  `runtime_audio.c`'s miniaudio node graph, not Simple.
- **No synth, no ADSR, no music sequencer/tracker, no WAV encoder, anywhere.** Grep for
  `sequencer|tracker|synthesiz|adsr` under audio code: zero hits. `runtime_audio.c` only does
  `ma_engine_init` / `ma_sound_init_from_file` — decode-only, no encode, no capture.
- `sound_contract.spl`'s `"SSND:"` codec check is a test fixture, not a real format.
- No `simple sound` CLI subcommand exists.

```
 [today]                              [gap]                        [smallest fix]
 AudioManager ── plays files ──┐
 BusGraph/Snapshots ── mixes ──┼── runtime, tested, real
 Doppler/Occlusion ── spatial ─┘
                                        │
                          ┌─────────────┴─────────────┐
                          │   no way to AUTHOR a new    │
                          │   sound/music asset in Simple│
                          └─────────────┬─────────────┘
                                        ▼
              WAV encoder extern → envelope/tone-gen → SDN format → `simple sound` CLI
```

**Do first**: WAV render path (deterministic, byte-assertable). **Skip for now**: full tracker,
HRTF wiring, GUI, capture/record — all YAGNI until a shipping game asks for them.

Full doc: `doc/01_research/app/game_tools/sound_music_effects.md`
