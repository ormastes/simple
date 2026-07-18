# Game2d Asset Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_asset_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_asset_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_asset_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_asset_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Asset Facade Specification

## Scenarios

### nogc_async_mut game2d asset facade

#### re-exports typed ids, diagnostics, and empty asset table behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = AssetId<text>.new("hero", 1)
expect(valid.key).to_equal("hero")
expect(valid.raw).to_equal(1)
expect(valid.is_valid()).to_equal(true)
expect(valid.eq(AssetId<text>.new("hero", 1))).to_equal(true)
val err = AssetError.missing(Span(line: 7, column: 3), "assets.sdn", "hero")
expect(err.code).to_equal("GAME-ASSET-001")
expect(err.diagnostic()).to_contain("hero")
val atlas = Atlas.new("sprites", 64, 32)
expect(atlas.image_width).to_equal(64)
val table = AssetTable.empty()
expect(table.images.len()).to_equal(0)
expect(table.sounds.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game2d/asset/game2d_asset_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut game2d asset facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
