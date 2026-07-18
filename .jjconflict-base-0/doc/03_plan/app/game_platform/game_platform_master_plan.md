# Game Platform Master Plan — production framework + tools for 2D/3D

Synthesis of six research/plan lanes (2026-07-03; opus/sonnet/haiku research,
fable review). Per-lane docs:

| Lane | Research | Plan |
|---|---|---|
| Image/object design | `doc/01_research/app/game_tools/image_object_design.md` | `doc/03_plan/app/game_tools/image_object_design_plan.md` |
| Sound/music/effects | `doc/01_research/app/game_tools/sound_music_effects.md` | `doc/03_plan/app/game_tools/sound_music_effects_plan.md` |
| Scene/map generation | `doc/01_research/app/game_tools/scene_map_generation.md` | `doc/03_plan/app/game_tools/scene_map_generation_plan.md` |
| Collision/physics | `doc/01_research/app/game_engine/collision_physics_audit.md` | `doc/03_plan/app/game_engine/collision_physics_plan.md` |
| Netcode | `doc/01_research/app/game_engine/netcode_prediction.md` | `doc/03_plan/app/game_engine/netcode_prediction_plan.md` |
| Game-library extraction | `doc/01_research/app/game_engine/game_library_extraction.md` | `doc/03_plan/app/game_engine/game_library_extraction_plan.md` |

## Verified headline findings (fable review re-checked these)

1. **The engine is big but the games bypass it.** breakout hand-rolls AABB
   collision next to a Box2D-class `engine/physics/` (broadphase, narrowphase,
   solver, joints, CCD, cloth, vehicle). Dogfooding is the cheapest hardening.
2. **`src/lib/common/net/` does not exist** yet `byte_cursor`/`addr` are
   imported by bgp/dtls/ipsec/ldap. Landing ByteReader/ByteWriter unbreaks four
   protocol modules AND is the netcode wire foundation. (Verified 2026-07-03.)
3. **No encoders anywhere**: image side has decoders only (no PNG/BMP encode,
   no DEFLATE compress); audio side has no WAV encode, no synthesis, no ADSR.
   Both encoders are pure-Simple work (bytes out), no runtime changes.
4. **Physics regressions + dead code**: 5/14 system specs fail on a deprecated
   `RawHandle.new()` ctor (verified: `physics_stacking_spec` fails today);
   `engine/physics2/` re-exports ~40 nonexistent submodules, has zero external
   callers (verified) → delete. CCD is implemented but never wired into
   `step()`. Duplicate `PhysicsWorld2D/3D` exports collide under wildcard.
5. **Determinism is already proven** (game2d loop + rollball bit-identical
   runs) — this is the enabler for rollback netcode and for every absolute
   BDD oracle in these plans.

## Phases (each lands with SSpec BDD; scenario outlines live in lane plans)

**P0 — repair + foundations (unblocks everything)**
- Fix `RawHandle.new()` in the 5 failing physics specs; delete `physics2/`;
  dedupe the double `PhysicsWorld2D/3D` exports.
- Land `src/lib/common/net/byte_cursor.spl` (ByteReader/ByteWriter).
- Land `src/lib/common/image/png_encode.spl` (stored-block DEFLATE first) and
  `src/lib/common/audio/wav_encode.spl` (pure Simple, fable-reviewed choice).

**P1 — library-of-game extraction (behavior-preserving)**
- Extract rollball's `find_centroid`/`diff_count`/`dump_ppm`/`composite_hud`
  and the session-harness skeleton into game2d/game3d libs; games become first
  consumers; all existing game specs stay green unchanged.
- Wire breakout onto `engine/physics` collision2d (replaces hand-rolled AABB);
  wire CCD into world step (fixes ball tunneling at speed).

**P2 — tool CLIs on the foundations**
- `spritesheet` CLI: existing `AtlasBuilder` + PNG encode + SDN manifest the
  asset loader already parses.
- `simple sound` CLI: SDN sound format → envelope/tone synth (pure Simple) →
  WAV render (byte-deterministic) → play via existing AudioManager.
- `model3d gen`: seeded `noise.spl` (value/Perlin + fBm) → heightmap-to-boxes
  SDN + CA-cave tilemap SDN, roundtripping through existing inspect/render and
  `TileMap.create`.

**P3 — netcode vertical slice**
- `game_net` lib: versioned wire frames on ByteReader/Writer; input buffer +
  prediction window + rewind-and-replay reconciler on the proven fixed step;
  transactional accept/reject/cancel layer; deterministic loopback harness
  with seeded latency/loss/reorder (no sockets in BDD).

**P4 — deferred by explicit YAGNI** (recorded in lane docs): WFC/L-systems/
marching-cubes, tracker-grade sequencer, GUI editors, HRTF offline render,
real-socket transport + interest management, GPU physics solver.

## Cross-lane dependency graph

byte_cursor → netcode wire, wav_encode
png_encode → spritesheet CLI, model3d textures
physics spec repair → breakout rewiring → extraction P1
determinism (done) → netcode reconciler, all byte-identical oracles

## Process note

Model split per goal directive: research/plan by opus (scene-gen, netcode),
sonnet (image, audio, physics), haiku (extraction); fable review corrected the
WAV-encoder-in-C plan item to pure Simple and re-verified findings 2–4 above
before landing.
