# bin/simple breakout smoke

> <details>

<!-- sdn-diagram:id=_binsimple_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_binsimple_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_binsimple_smoke_spec -> std
_binsimple_smoke_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_binsimple_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bin/simple breakout smoke

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/game2d/_binsimple_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### breakout smoke on deployed binary

#### constructs and has 32 bricks

- var g = Game new game
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g = Game.new_game()
assert_equal(g.bricks.len(), 32)
assert_equal(g.state, GameState.Menu)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
