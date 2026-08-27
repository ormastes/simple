# Seeded Noise (Perlin/fBm)

> `std.common.math.noise` provides seeded, pure gradient (Perlin) noise and fractal Brownian motion (fBm) for procedural scene/map generation (heightmaps, etc.). The permutation table (`Perm`) is built once from a seed via an internal hash — sampling never touches shared mutable state, so results only depend on the seed and the coordinates queried, never on call order.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns exactly 0.0 at every integer lattice point
- Sample noise2 across a 7x7 grid of integer coordinates
- Then every lattice sample is exactly zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns exactly 0.0 at every integer lattice point")
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

- is bounded in [-1, 1] over a sampled grid
- Sample noise2 at 400 non-lattice points
- Then every sample stays within [-1, 1]


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is bounded in [-1, 1] over a sampled grid")
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

- is seed-deterministic: same seed always yields the pinned constant
- Sample fbm2 at a fixed non-lattice coordinate for seed 42
- Then it matches the recorded KAT constant exactly
   - Expected: v equals `0.11953125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is seed-deterministic: same seed always yields the pinned constant")
step("Sample fbm2 at a fixed non-lattice coordinate for seed 42")
val p = perm_new(42)
val v = fbm2(p, 3.5, 7.25, 4, 2.0, 0.5)

step("Then it matches the recorded KAT constant exactly")
expect(v).to_equal(0.11953125)
```

</details>

#### diverges across seeds

- diverges across seeds
- Sample fbm2 at the same coordinate for seeds 42 and 43
- Then the two seeds produce clearly different values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("diverges across seeds")
step("Sample fbm2 at the same coordinate for seeds 42 and 43")
val v42 = fbm2(perm_new(42), 3.5, 7.25, 4, 2.0, 0.5)
val v43 = fbm2(perm_new(43), 3.5, 7.25, 4, 2.0, 0.5)

step("Then the two seeds produce clearly different values")
assert_true(_abs(v42 - v43) > 0.01)
```

</details>

### noise3

#### returns exactly 0.0 at every integer lattice point

- returns exactly 0.0 at every integer lattice point
- Sample noise3 across a small cube of integer coordinates
- Then every lattice sample is exactly zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns exactly 0.0 at every integer lattice point")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b29963abfd75ef11872eb461fcbbafb452c896fa67824e2ab2748becdaa669b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b29963abfd75ef11872eb461fcbbafb452c896fa67824e2ab2748becdaa669b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b29963abfd75ef11872eb461fcbbafb452c896fa67824e2ab2748becdaa669b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/game_tools/noise_spec.spl
mirror: doc/06_spec/01_unit/app/game_tools/noise_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/game_tools/noise_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/game_tools/noise_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/game_tools/noise_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/game_tools/noise_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exactly 0.0 at every integer lattice point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/game_tools/noise_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is bounded in [-1, 1] over a sampled grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/game_tools/noise_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is seed-deterministic: same seed always yields the pinned constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
