# Scene/Map Generation Plan — TL;DR

Smallest production slice: seeded noise → SDN `gen` CLI → roundtrip.

**Top 3 items**
1. `src/lib/common/math/noise.spl` — seeded `noise2/noise3` + `fbm2` (pure,
   own permutation hash, reuses `math.spl` lerp/floor). LCG stays for dice only.
2. `simple model3d gen` in `src/app/model3d/main.spl` — `gen heightmap`
   (fbm→box-per-column SDN) and `gen tilemap` (CA 4-5 rule → `[[i32]]` SDN).
3. Roundtrip: heightmap SDN reuses existing `model3d inspect/render` (zero new
   loader); tilemap SDN → `TileMap.create` via a thin reader in `game2d/config/`.

**BDD oracles (absolute):** noise2 == 0.0 at integer lattice; fbm KAT constant
pinned; same-seed ⇒ byte-identical file; cross-seed divergence > K%; CA fixpoint
+ no-isolated-cell invariant + floor reachability; WFC (later) no adjacency
violation across whole map.

```
P1 noise ─► P2 gen(heightmap|tilemap) ─► P3 roundtrip (inspect/render, TileMap)
        deferred: WFC · Poisson · L-systems · marching cubes
```
