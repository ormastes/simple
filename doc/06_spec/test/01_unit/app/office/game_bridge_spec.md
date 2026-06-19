# Game Bridge Specification

> <details>

<!-- sdn-diagram:id=game_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game_bridge_spec -> std
game_bridge_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Bridge Specification

## Scenarios

### game bridge: declared office connections

#### lists calc, draw, and db as connection targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conns = game_office_connections()
expect(conns).to_contain("calc")
expect(conns).to_contain("draw")
expect(conns).to_contain("db")
```

</details>

#### reports calc, draw, and db as implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val live = game_implemented_connections()
expect(live.len()).to_equal(3)
expect(live).to_contain("calc")
expect(live).to_contain("draw")
expect(live).to_contain("db")
```

</details>

### game bridge: Calc token data
_Calc cells become deterministic game level/tuning tokens._

#### exports referenced Calc cells as game tokens

- sheet set value
- sheet set value
- sheet set value
   - Expected: calc_row_to_game_tokens(sheet, ["A1", "B1", "C1"]) equals `wall floor door`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Level")
sheet.set_value("A1", "wall")
sheet.set_value("B1", "floor")
sheet.set_value("C1", "door")
expect(calc_row_to_game_tokens(sheet, ["A1", "B1", "C1"])).to_equal("wall floor door")
```

</details>

### game bridge: Draw sprite data
_SDD Draw nodes become deterministic sprite records for a game tool._

#### exports SDD nodes as game sprite records

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sprites = draw_sdd_to_game_sprites("graph: Level\nplayer: Player @hero shape: circle x: 10 y: 20 width: 16 height: 16 layer: 2\ndoor: Door x: 40 y: 20 width: 12 height: 24")
expect(sprites.len()).to_equal(2)
expect(sprites).to_contain("sprite player label=Player shape=circle style=hero rect=10,20,16,16 layer=2")
expect(sprites).to_contain("sprite door label=Door shape=rect style=default rect=40,20,12,24 layer=0")
```

</details>

#### exports a newline-separated sprite manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = draw_sdd_to_game_sprite_manifest("graph: Level\nspawn: Spawn x: 1 y: 2 width: 3 height: 4")
expect(manifest).to_contain("sprite spawn")
expect(manifest).to_contain("rect=1,2,3,4")
```

</details>

### game bridge: Base state data
_Base exact-match query rows become game state records._

#### exports matched Base rows as key value records

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = base_query_to_game_records(_game_table(), "scope", "level1", "key", "value")
expect(records.len()).to_equal(2)
expect(records).to_contain("hp=100")
expect(records).to_contain("spawn=gate")
```

</details>

#### exports a compact game state line and fails closed for missing columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = base_query_to_game_state(_game_table(), "scope", "level1", "key", "value")
val missing = base_query_to_game_records(_game_table(), "scope", "level1", "missing", "value")
expect(state).to_contain("hp=100")
expect(state).to_contain("spawn=gate")
expect(missing.len()).to_equal(0)
```

</details>

#### summarizes the Base table exposed to game tooling

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(base_table_game_summary(_game_table())).to_equal("db game_state rows=3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/game_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- game bridge: declared office connections
- game bridge: Calc token data
- game bridge: Draw sprite data
- game bridge: Base state data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
