# doomgeneric Port — Honest Status (2026-08-19)

`src/lib/nogc_sync_mut/game2d/ports/doomgeneric.spl` (pure Simple, ~545 lines).

## What IS real (implemented, spec-covered)

| Subsystem | Status |
|---|---|
| WAD header parsing | Real: IWAD/PWAD magic, lump count, directory offset; little-endian; fail-closed on truncation/bad magic/out-of-bounds lumps |
| Lump directory walk | Real: `wad_parse` builds the full lump table; `wad_map_lump` extracts a MAPxx lump scoped between map markers |
| Map lumps | Real: THINGS (10-byte records), LINEDEFS (14-byte, dangling-vertex-ref rejected), VERTEXES (signed i16 pairs); record-size validated, fail-closed |
| Player spawn | From THINGS type 1 (position + angle) |
| Movement/collision | Segment-vs-linedef crossing test blocks movement through walls |
| Renderer | 2.5D column raycaster over actual LINEDEFS/VERTEXES: per-column ray (dir + camera plane) vs linedef segments, wall height from perpendicular distance, continuous distance shading, deterministic palette |
| Determinism | frame FNV hash stable; backend parity (headless / web_canvas / gui_engine2d byte-identical) holds — `test/03_system/engine/game2d_doomgeneric_backend_parity_spec.spl` |

No IWAD ships in-repo: `proof_wad()` builds a synthetic but structurally VALID
one-map IWAD (MAP01, 6 vertexes, 5 linedefs, 1 thing) byte-by-byte.

## What is ABSENT vs real doomgeneric (do not overclaim)

- SECTORS/SIDEDEFS: no floor/ceiling heights, no light levels
- BSP/NODES/SEGS/SSECTORS: renderer brute-forces all linedefs, no BSP traversal
- Textures and flats (PLAYPAL/TEXTUREx/patches): palette is synthetic
- Things rendering and enemy AI, weapons beyond a shot counter
- Sound, menus, demo playback, savegames
- Only 4 cardinal view angles (quarter-turn look), no fine rotation

## Specs

- `test/01_unit/lib/nogc_sync_mut/game2d/ports/doomgeneric_spec.spl` (+ `test/unit/...` mirror): 15 examples — WAD valid/bad-magic/truncated header/truncated directory, lump extraction, record parsing, misaligned/dangling-ref rejection, THINGS spawn, collision blocking, wall-column projection, determinism, map-load fail-closed rendering.
- `test/03_system/engine/game2d_doomgeneric_backend_parity_spec.spl`: 2 examples, byte-identical frame_hash across three backends.
