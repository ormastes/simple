# Game2d Doomgeneric Port Specification

> <details>

<!-- sdn-diagram:id=game2d_doomgeneric_port_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_doomgeneric_port_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_doomgeneric_port_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_doomgeneric_port_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Doomgeneric Port Specification

## Scenarios

### Doomgeneric-style game port proof

#### keeps the example on the pure std.game2d surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/doomgeneric/main.spl")
expect(src.contains("use std.game2d as g")).to_equal(true)
expect(src.contains("rt_sdl2_")).to_equal(false)
expect(src.contains("Steamworks")).to_equal(false)
```

</details>

#### proves WAD bytes, input tick, and video frame in one path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = dg.DoomPortState.boot(dg.proof_wad())
val s1 = dg.doom_tick(s0, dg.DoomPortInput(forward: true, back: false, turn_left: false, turn_right: false, fire: true))
val frame = dg.render_frame(s1, 160, 100)
expect(s1.wad_bytes).to_equal(12)
expect(s1.tick).to_equal(1)
expect(s1.shots).to_equal(1)
expect(frame.non_black_count()).to_equal(160 * 100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/game2d_doomgeneric_port_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Doomgeneric-style game port proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
