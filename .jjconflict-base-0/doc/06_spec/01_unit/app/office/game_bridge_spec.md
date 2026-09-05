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
| 2 | 2 | 0 | 0 |

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

#### honestly implements only the calc connection so far

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val live = game_implemented_connections()
expect(live.len()).to_equal(1)
expect(live).to_contain("calc")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
