# Game2d Config Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_config_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_config_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_config_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_config_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Config Facade Specification

## Scenarios

### gc_async_mut game2d config facade

#### re-exports game configuration defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val window = WindowConfig.default()
expect(window.width).to_equal(800)
expect(window.height).to_equal(600)
expect(window.vsync).to_equal(true)

val runtime = RuntimeConfig.default()
expect(runtime.fixed_step_hz).to_equal(60)
expect(runtime.max_entities).to_equal(1024)

val config = GameConfig.default()
expect(config.title).to_equal("Simple Game")
expect(config.startup_scene).to_equal("main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d config facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
