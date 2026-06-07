# Doomgeneric Specification

> <details>

<!-- sdn-diagram:id=doomgeneric_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doomgeneric_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doomgeneric_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doomgeneric_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doomgeneric Specification

## Scenarios

### doomgeneric port proof

#### boots from a WAD-like byte buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = dg.DoomPortState.boot(dg.proof_wad())
expect(state.wad_bytes).to_equal(12)
expect(state.tick).to_equal(0)
```

</details>

#### advances deterministic ticks and input movement

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = dg.DoomPortState.boot(dg.proof_wad())
val input = dg.DoomPortInput(forward: true, back: false, turn_left: false, turn_right: false, fire: true)
val s1 = dg.doom_tick(s0, input)
expect(s1.tick).to_equal(1)
expect(s1.shots).to_equal(1)
expect(s1.x > s0.x).to_equal(true)
```

</details>

#### turns without host APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = dg.DoomPortState.boot(dg.proof_wad())
val input = dg.DoomPortInput(forward: false, back: false, turn_left: false, turn_right: true, fire: false)
val s1 = dg.doom_tick(s0, input)
expect(s1.angle).to_equal(1)
```

</details>

#### renders deterministic non-black software frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = dg.DoomPortState.boot(dg.proof_wad())
val frame1 = dg.render_frame(state, 160, 100)
val frame2 = dg.render_frame(state, 160, 100)
expect(frame1.non_black_count()).to_equal(160 * 100)
expect(frame1.hash()).to_equal(frame2.hash())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/game2d/ports/doomgeneric_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- doomgeneric port proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
