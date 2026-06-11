# Game2d App Facade Specification

> 1. defaults load

<!-- sdn-diagram:id=game2d_app_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_app_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_app_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_app_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d App Facade Specification

## Scenarios

### nogc_async_mut game2d app facade

#### re-exports app defaults and config records

1. defaults load
   - Expected: window.width equals `800`
   - Expected: window.height equals `600`
   - Expected: window.vsync is true
   - Expected: runtime.fixed_step_hz equals `60`
   - Expected: runtime.deterministic is false
   - Expected: config.title equals `Simple Game`
   - Expected: config.window.width equals `800`
   - Expected: config.runtime.max_entities equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defaults = AppDefaults.new()
defaults.load()

val window = WindowConfig.default()
expect(window.width).to_equal(800)
expect(window.height).to_equal(600)
expect(window.vsync).to_equal(true)

val runtime = RuntimeConfig.default()
expect(runtime.fixed_step_hz).to_equal(60)
expect(runtime.deterministic).to_equal(false)

val config = GameConfig.default()
expect(config.title).to_equal("Simple Game")
expect(config.window.width).to_equal(800)
expect(config.runtime.max_entities).to_equal(1024)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game2d/app/game2d_app_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut game2d app facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
