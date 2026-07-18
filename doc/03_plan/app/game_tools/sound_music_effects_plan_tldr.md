# TL;DR — Sound/Music Tooling Plan

Smallest viable authoring loop, reusing existing engine code, no GUI/tracker/capture.

```
 SDN file ──parse (reuse src/lib/common/sdn)──▶ sample buffer (envelope+tone-gen, new pure-Simple)
                                                        │
                                    apply EffectsChain (reuse effects.spl, offline ma_engine)
                                                        │
                                        WAV encode (new rt_audio_encode_wav_f32 extern)
                                                        │
                                   `simple sound validate|render|play` CLI (new dispatch entry)
```

## Top 3 items
1. **WAV encoder extern** (`runtime_audio.c` + `audio_sffi.spl` wrapper) — unblocks every
   deterministic test oracle; nothing else can be verified without it.
2. **SDN sound format + `simple sound render`** — reuse `src/lib/common/sdn/*` and the
   `game_sdn.spl` loader pattern; the actual describe-once/render-reproducibly loop.
3. **Envelope/tone-gen primitives + effects-chain wiring** — turns `render` into something
   more than a raw file copy or flat tone.

`validate`/`play` subcommands and multi-event "sequence" SDN shape ship after 1–3 prove out.

BDD oracles are all numeric: exact sample values, exact envelope breakpoints, byte-identical
re-renders — never "plays fine."

Full doc: `doc/03_plan/app/game_tools/sound_music_effects_plan.md`
