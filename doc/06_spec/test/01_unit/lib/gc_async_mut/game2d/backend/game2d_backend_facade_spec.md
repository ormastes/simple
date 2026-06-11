# Game2d Backend Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_backend_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_backend_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_backend_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_backend_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Backend Facade Specification

## Scenarios

### gc_async_mut game2d backend facade

#### re-exports deterministic backend records and hash helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(frame_hash([])).to_equal(FNV_OFFSET_BASIS)
expect(frame_hash_hex([]).len()).to_equal(18)
val cfg = WindowConfig.default()
expect(cfg.width).to_equal(800)
expect(Window.null().raw).to_equal(0)
expect(Event.none().kind).to_equal("none")
val backend = HeadlessBackend.create(2, 2)
expect(backend.width).to_equal(2)
expect(backend.golden_diff(backend.frame_hash())).to_equal("")
val sdl = SdlBackend.create()
expect(sdl.width).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/backend/game2d_backend_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d backend facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
