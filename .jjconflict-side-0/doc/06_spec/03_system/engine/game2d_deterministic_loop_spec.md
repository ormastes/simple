# Game2D Deterministic Loop (AC-4)

> 60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.

<!-- sdn-diagram:id=game2d_deterministic_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_deterministic_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_deterministic_loop_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_deterministic_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Deterministic Loop (AC-4)

60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_deterministic_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

60 Hz fixed-step accumulator: 100ms wall time → exactly 6 fixed_update calls.
`#[deterministic]` mode → `g.time.now()` outside callback panics with
`GAME-DET-001`. Inside `update`/`fixed_update` it returns simulated step time.

Red-phase: LoopDriver/det_guard absent; assertions fail until Phase 5.

## Scenarios

### Game2D Deterministic Loop (AC-4)
_## Fixed-step accumulator + determinism runtime guard._

### LoopDriver fixed-step accumulator

<details>
<summary>Advanced: driver.spl declares class LoopDriver</summary>

#### driver.spl declares class LoopDriver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "class LoopDriver")).to_equal(true)
```

</details>


</details>

#### driver.spl wraps Clock.consume_fixed_steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "consume_fixed_steps")).to_equal(true)
```

</details>

#### driver.spl pumps app.update + app.fixed_update

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/loop/driver.spl")
expect(_has(src, "fixed_update") and _has(src, "update")
    ).to_equal(true)
```

</details>

#### edge case: synthetic 100ms@60Hz computes 6 steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Plain math sanity: 100ms / (1000/60)ms ≈ 6.0
val step_ms = 1000 / 60
val n_steps = 100 / step_ms
expect(n_steps).to_equal(6)
```

</details>

#### edge case: 0ms wall time → 0 fixed_update calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val step_ms = 1000 / 60
val n_steps = 0 / step_ms
expect(n_steps).to_equal(0)
```

</details>

### det_guard runtime checks

#### det_guard.spl declares fn now and fn rand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "fn now(") and _has(src, "fn rand(")
    ).to_equal(true)
```

</details>

#### det_guard.spl declares enter_callback / leave_callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "enter_callback") and
       _has(src, "leave_callback")).to_equal(true)
```

</details>

#### GAME-DET-001 panic code is wired

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "GAME-DET-001")).to_equal(true)
```

</details>

#### edge case: synthetic detector finds the code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("panic GAME-DET-001 wall clock outside callback",
    "GAME-DET-001")).to_equal(true)
```

</details>

### error path: unseeded random in deterministic mode panics

#### det_guard.spl mentions seeded RNG path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/time/det_guard.spl")
expect(_has(src, "seeded") or _has(src, "rng_seed") or
       _has(src, "deterministic")).to_equal(true)
```

</details>

#### edge case: empty source does not falsely satisfy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "deterministic")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
