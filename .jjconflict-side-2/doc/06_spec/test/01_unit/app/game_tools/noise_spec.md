# Seeded Noise (Perlin/fBm)

> `std.common.math.noise` provides seeded, pure gradient (Perlin) noise and fractal Brownian motion (fBm) for procedural scene/map generation (heightmaps, etc.). The permutation table (`Perm`) is built once from a seed via an internal hash — sampling never touches shared mutable state, so results only depend on the seed and the coordinates queried, never on call order.

<!-- sdn-diagram:id=noise_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=noise_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

noise_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=noise_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Seeded Noise (Perlin/fBm)

`std.common.math.noise` provides seeded, pure gradient (Perlin) noise and fractal Brownian motion (fBm) for procedural scene/map generation (heightmaps, etc.). The permutation table (`Perm`) is built once from a seed via an internal hash — sampling never touches shared mutable state, so results only depend on the seed and the coordinates queried, never on call order.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #scene-map-gen-noise |
| Category | Stdlib / Procedural Generation |
| Status | Implemented |
| Source | `test/01_unit/app/game_tools/noise_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`std.common.math.noise` provides seeded, pure gradient (Perlin) noise and
fractal Brownian motion (fBm) for procedural scene/map generation (heightmaps,
etc.). The permutation table (`Perm`) is built once from a seed via an
internal hash — sampling never touches shared mutable state, so results only
depend on the seed and the coordinates queried, never on call order.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `Perm` | Seeded permutation table, built once via `perm_new(seed)` |
| Lattice zero | `noise2`/`noise3` are exactly `0.0` at every integer coordinate |
| `fbm2` | Sum of octaves of `noise2` at increasing frequency, decreasing amplitude, normalized |
| KAT | Known-answer test — an exact constant pinned from one reference run |

## Scenarios

### noise2

#### returns exactly 0.0 at every integer lattice point

- Sample noise2 across a 7x7 grid of integer coordinates
- Then every lattice sample is exactly zero
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sample noise2 across a 7x7 grid of integer coordinates")
val p = perm_new(42)
var all_zero = true
var i: i64 = -3
while i <= 3:
    var j: i64 = -3
    while j <= 3:
        if noise2(p, i as f64, j as f64) != 0.0:
            all_zero = false
        j = j + 1
    i = i + 1

step("Then every lattice sample is exactly zero")
assert_true(all_zero)
```

</details>

#### is bounded in [-1, 1] over a sampled grid

- Sample noise2 at 400 non-lattice points
- Then every sample stays within [-1, 1]
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sample noise2 at 400 non-lattice points")
val p = perm_new(7)
var in_range = true
var i: i64 = 0
while i < 20:
    var j: i64 = 0
    while j < 20:
        val v = noise2(p, (i as f64) * 0.37 + 0.11, (j as f64) * 0.29 + 0.07)
        if (v < -1.0 or v > 1.0):
            in_range = false
        j = j + 1
    i = i + 1

step("Then every sample stays within [-1, 1]")
assert_true(in_range)
```

</details>

#### is seed-deterministic: same seed always yields the pinned constant

- Sample fbm2 at a fixed non-lattice coordinate for seed 42
- Then it matches the recorded KAT constant exactly
   - Expected: v equals `0.11953125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sample fbm2 at a fixed non-lattice coordinate for seed 42")
val p = perm_new(42)
val v = fbm2(p, 3.5, 7.25, 4, 2.0, 0.5)

step("Then it matches the recorded KAT constant exactly")
expect(v).to_equal(0.11953125)
```

</details>

#### diverges across seeds

- Sample fbm2 at the same coordinate for seeds 42 and 43
- Then the two seeds produce clearly different values
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sample fbm2 at the same coordinate for seeds 42 and 43")
val v42 = fbm2(perm_new(42), 3.5, 7.25, 4, 2.0, 0.5)
val v43 = fbm2(perm_new(43), 3.5, 7.25, 4, 2.0, 0.5)

step("Then the two seeds produce clearly different values")
assert_true(_abs(v42 - v43) > 0.01)
```

</details>

### noise3

#### returns exactly 0.0 at every integer lattice point

- Sample noise3 across a small cube of integer coordinates
- Then every lattice sample is exactly zero
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sample noise3 across a small cube of integer coordinates")
val p = perm_new(9)
var all_zero = true
var i: i64 = 0
while i <= 2:
    var j: i64 = 0
    while j <= 2:
        var k: i64 = 0
        while k <= 2:
            if noise3(p, i as f64, j as f64, k as f64) != 0.0:
                all_zero = false
            k = k + 1
        j = j + 1
    i = i + 1

step("Then every lattice sample is exactly zero")
assert_true(all_zero)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
