# Scene/Map Generation — Mathematical Procedural Content Research

Status: research (no implementation). Scope: 2D map + 3D scene generation and
seeded mathematical (procedural) generation for the Simple game platform.

## 1. Local infrastructure inventory (what already exists)

| Concern | File | Notes |
|---|---|---|
| 3D scene CLI + SDN format | `src/app/model3d/main.spl` (520 ln) | `scene:{name,background,camera:{eye,target,fov_deg},nodes:[{name,shape:"box",center[3],size[3],color}]}`; subs `inspect`/`render`; only `box` shape; every field validated (trust boundary). |
| Scene fixtures | `test/fixtures/model3d/valid_scene.sdn` | Canonical SDN sample; box + floor. |
| Seeded PRNG | `src/lib/common/random_pure.spl` (87 ln) | LCG: `lcg_rng(seed)`, `lcg_next()`, `randint`, `random()->[0,1)`. Deterministic, shared-state. |
| Math primitives | `src/lib/common/math/math.spl` (109 ln) | `math_sin/cos/floor/sqrt/pow/lerp/clamp/min/max/round`. No noise. |
| Heightmap sink (3D) | `src/lib/nogc_sync_mut/engine/render/terrain.spl` | `TerrainData` grid, `set_height/get_height/sample_height/raise/flatten_area`. |
| Tilemap sink (2D) | `src/lib/{gc_async_mut,nogc_sync_mut}/…/tilemap.spl` | `TileMap.create(tid,tw,th,cells:[[i32]])`; `-1`=empty. |
| Scene graph | `src/lib/nogc_sync_mut/engine/scene/{node,node3d,tree,serializer,prefab}.spl`; `src/lib/gc_async_mut/gpu/engine3d/scene_graph3d.spl` | Serializer already exists. |
| Game config SDN | `src/lib/nogc_sync_mut/game2d/config/game_sdn.spl` | SDN→GameConfig loader pattern to mirror. |
| Rollball course | `examples/11_advanced/game3d_rolling/main.spl` | Box-emit game; no reusable `submit_box` helper found. |

**Gap:** no noise / fBm / Perlin / simplex / WFC / Poisson / cellular-automata /
BSP / L-system code anywhere. Sinks (tilemap `[[i32]]`, `TerrainData`, box-node
SDN) and a seeded PRNG exist — generators do not.

**PRNG caveat:** `random_pure` is a *shared-state LCG*. LCG low bits are weak and
call-order-dependent — unusable for lattice gradient noise (needs
position→gradient hashing independent of call order). Noise must carry its own
integer hash / permutation table; LCG stays fine for scatter/CA/BSP dice.

## 2. Mathematical generation toolkit (researched, ranked for indie-scale prod)

Ranking = production value ÷ implementation cost against the *existing* SDN +
tile/heightmap infra. Every entry must be seed-deterministic (testability).

| Rank | Technique | Feeds | Est. size | Determinism | Verdict |
|---|---|---|---|---|---|
| 1 | **Value/Perlin noise + fBm** | heightmap→boxes (3D), tile thresholds (2D) | ~120–160 ln | permutation table from seed; position-pure | **Ship first.** Foundational for both dims. |
| 2 | **Cellular automata caves (4-5 rule)** | `[[i32]]` tilemap directly | ~40–60 ln | seed fill + fixed iterations | **Ship first.** Tiny; operates on existing cells. |
| 3 | **BSP room splitting** | tilemap rooms + corridors | ~80–120 ln | seeded split ratios | **Ship second.** Rectangular dungeons; classic. |
| 4 | **Poisson-disk (Bridson 2007)** | object scatter → box/prop scene nodes | ~90–130 ln | LCG-driven active list | Second wave. Blue-noise foliage/props. |
| 5 | **WFC simple tiled model** | constraint-consistent 2D maps | ~220–320 ln | seeded entropy pick + propagation | Defer. Highest complexity/payoff; own milestone. |
| 6 | **Maze (recursive backtracker)** | corridor `[[i32]]` | ~50 ln | seeded stack | Cheap nice-to-have alongside BSP. |
| 7 | **L-systems + turtle** | vegetation meshes | ~80 ln rewrite + turtle→box | deterministic string rewrite | Defer; needs mesh/turtle path. |
| 8 | **SDF composition + marching cubes** | arbitrary 3D meshes | ~300+ ln | pure sampling | Defer. Heightmap-to-boxes covers the 3D slice cheaply. |

### Technique notes (with sources)

- **Perlin/simplex noise:** Perlin's Improved Noise (SIGGRAPH 2002) fixed
  interpolation/gradient artifacts; simplex (2001) lowers cost in higher dims.
  Gustavson's *Simplex Noise Demystified* is the readable reference (C/Java/GLSL).
  2D: 8–16 gradients around the unit circle. **Key test property:** gradient
  (Perlin) noise is exactly `0` at every integer lattice point — a free
  known-answer oracle. fBm = Σ noise(f·2ⁱ)·(g)ⁱ over octaves.
- **WFC (Gumin):** tiled model (hand-authored edge adjacencies) vs overlapping
  model (3×3 sample patterns). Loop: collapse the min-Shannon-entropy cell,
  propagate adjacency constraints. Tiled model is the tractable first cut.
- **Poisson-disk (Bridson 2007):** O(n) via a spatial grid + active list; yields
  blue-noise spacing (`r` min distance). Standard for foliage/prop scatter.
- **CA caves:** random fill p≈0.45, then 4-5 rule (wall if ≥4/≥5 wall neighbors)
  for ~4–5 iterations → organic caves. Stochastic, seed-reproducible.
- **BSP dungeons:** recursively split rect, random axis + ratio, place a room in
  each leaf, connect siblings — popularized by RogueBasin. Combine BSP rooms +
  maze/drunkard corridors + CA for organic feel.

## 3. Fit to Simple

Chosen slice (noise+fBm, CA, BSP) reuses `math.spl` (sin/floor/lerp/clamp),
seeds off `random_pure`, and writes into the *already-validated* box-node SDN
(`model3d`) and `[[i32]]` tilemap cells. No new runtime, no new dependency, no
tier violation — noise/fBm/CA/BSP are pure functions living in
`src/lib/common/` (tier-neutral). WFC / Poisson / marching-cubes are strictly
larger and deferred to later milestones. See plan doc.

## Sources
- [Perlin — Improved Noise reference](https://mrl.cs.nyu.edu/~perlin/noise/)
- [Gustavson — Simplex Noise Demystified (PDF)](https://cgvr.cs.uni-bremen.de/teaching/cg_literatur/simplexnoise.pdf)
- [Simplex noise — Wikipedia](https://en.wikipedia.org/wiki/Simplex_noise)
- [BorisTheBrave — WFC Explained](https://www.boristhebrave.com/2020/04/13/wave-function-collapse-explained/)
- [Bridson — Fast Poisson Disk Sampling (SIGGRAPH)](https://history.siggraph.org/learning/fast-poisson-disk-sampling-in-arbitrary-dimensions-by-bridson/)
- [Extreme Learning — improved Bridson Poisson disc](https://extremelearning.com.au/an-improved-version-of-bridsons-algorithm-n-for-poisson-disc-sampling/)
- [RogueBasin — Cellular Automata caves](https://www.roguebasin.com/index.php/Cellular_Automata_Method_for_Generating_Random_Cave-Like_Levels)
- [RogueBasin — Basic BSP Dungeon generation](https://www.roguebasin.com/index.php/Basic_BSP_Dungeon_generation)
- [Liapis — PCG Book: Constructive dungeon generation](https://antoniosliapis.com/articles/pcgbook_dungeons.php)
