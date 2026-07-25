# Scene/Map Generation — TL;DR

Procedural (mathematical, seeded) 2D-map + 3D-scene generation for the game
platform. Sinks already exist; generators do not.

**Have:** `model3d` box-node SDN scene format (`src/app/model3d/main.spl`),
`TileMap [[i32]]`, `TerrainData` heightmap, seeded LCG (`random_pure.spl`),
`math.spl` (sin/floor/lerp/clamp). **Missing:** all noise/WFC/CA/BSP/Poisson.

**Toolkit ranked (value ÷ cost):** 1 value/Perlin noise + fBm · 2 cellular-
automata caves · 3 BSP dungeons · 4 Poisson-disk scatter · 5 WFC (defer) ·
6 maze · 7 L-systems (defer) · 8 SDF+marching-cubes (defer).

**Ship first = 1+2+3**: pure fns in `src/lib/common/`, seed-deterministic,
emit into existing SDN + tilemap cells. LCG is call-order-dependent → noise
needs its own permutation hash. Free test oracle: Perlin noise = 0 at integer
lattice points.

```
 seed ─┬─► noise/fBm ──► heightmap ──► box-node SDN ──► model3d inspect/render
       ├─► CA (4-5)   ──► [[i32]] tilemap ──► game2d TileMap.create
       └─► BSP split  ──► rooms+corridors ─┘
        (deterministic: same seed ⇒ byte-identical output)
```
