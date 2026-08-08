# Scene/Map Generation — Plan (smallest production slice)

Research: `doc/01_research/app/game_tools/scene_map_generation.md`.
Scope of this plan: the smallest shippable slice = seeded noise/fBm + a `gen`
CLI emitting SDN + one roundtrip. Docs-only; no code changed yet.

## Deliverables (3 core items)

### P1 — Seeded noise + fBm (tier-neutral pure lib)
New file `src/lib/common/math/noise.spl` (est. ~150 ln):
- `Perm` permutation table built from a seed (integer hash / splitmix, **not**
  the shared LCG — noise must be position-pure, call-order-independent).
- `noise2(perm, x, y) -> f64`, `noise3(perm, x, y, z) -> f64` (gradient/Perlin).
- `fbm2(perm, x, y, octaves, lacunarity, gain) -> f64`.
- Reuse `math.spl`: `math_floor`, `math_lerp` (already exists), smoothstep local.
- Keep `random_pure` LCG for scatter/CA/BSP dice only.

### P2 — `simple model3d gen` subcommand (SDN emitter)
Extend `src/app/model3d/main.spl` (mirror the existing `Scene3`/`Node3` box
writer; reuse validation types):
- `gen heightmap --seed N --w W --d D --out scene.sdn` — sample `fbm2` per cell,
  emit one box per column (height→`size.y`, `center.y=h/2`), color by height band.
- `gen tilemap --seed N --w W --h H --out map.sdn` — CA caves (4-5 rule) →
  `[[i32]]` → SDN `{ tilemap: { cols, rows, cells: [[…]] } }` matching what a
  `game2d` loader reads (align with `game_sdn.spl` conventions).
- BSP variant behind `--mode bsp` for the tilemap path (P3-adjacent, small).

### P3 — Roundtrip verification
- Generated heightmap SDN loads via existing `model3d inspect` / `render`
  unchanged (it is already box-node SDN — zero new loader).
- Generated tilemap SDN → `TileMap.create` (add a thin SDN→`[[i32]]` reader in
  `game2d/config/` next to `game_sdn.spl` if not already covered).

## Sequencing
1. P1 noise lib + its spec (independent, no CLI).
2. P2 heightmap `gen` (reuses existing box SDN loader → cheapest roundtrip).
3. P2 tilemap `gen` (CA) + P3 tilemap reader.
4. BSP mode. WFC / Poisson / marching-cubes = separate later milestones.

## BDD — SSpec (describe/it with absolute oracles)

`test/app/game_tools/noise_spec.spl`:
- describe "noise2" → it "returns exactly 0.0 at every integer lattice point"
  (gradient-noise property; assert `noise2(p, i, j) == 0.0` for a grid of ints).
- it "is bounded in [-1, 1] over a sampled grid".
- it "is seed-deterministic: same seed ⇒ identical value at a fixed coord"
  (pin `fbm2(seed=42, 3.5, 7.25, 4, 2.0, 0.5)` to a recorded constant — KAT).
- it "diverges across seeds" (seed 42 vs 43 differ at that coord by > ε).

`test/app/game_tools/scene_gen_spec.spl`:
- describe "gen heightmap" → it "emits SDN that `model3d inspect` accepts"
  (roundtrip: generate → inspect exits 0, node count == W*D).
- it "is byte-identical for the same seed" (two runs ⇒ identical file bytes).
- it "differs across seeds" (seed 1 vs 2 ⇒ > K% of node heights differ —
  divergence control, not just inequality).

`test/app/game_tools/tilemap_gen_spec.spl`:
- describe "CA cave gen" → it "reaches a fixpoint: extra iteration changes 0 cells".
- it "has no isolated single-cell wall or floor" (4-5 rule invariant scan over
  the whole map — no neighborhood violation anywhere).
- it "keeps all floor reachable" (single connected floor region; flood-fill).
- describe "BSP gen" → it "produces non-overlapping rooms within bounds".
- (WFC, when added) it "has no adjacent-tile constraint violation across the
  whole map" (full-grid adjacency scan) + same-seed byte-identical output.

Oracle policy: prefer *absolute* checks (integer-lattice zero, bounded range,
fixpoint, invariant scans, byte-identity) over golden images. KAT constants are
recorded once from the reference impl and pinned as regression anchors.

## Constraints / non-goals
- Pure `.spl` only; noise/CA/BSP live in `src/lib/common/` (tier-neutral).
- No new runtime symbol, no new dependency, no new SDN dialect for heightmaps
  (reuse box-node scene). Tilemap SDN aligns with `game2d` conventions.
- Deferred (own milestones): WFC, Poisson scatter, L-systems, marching cubes.
