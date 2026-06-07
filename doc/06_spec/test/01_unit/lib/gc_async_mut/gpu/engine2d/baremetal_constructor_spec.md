# Baremetal Constructor Specification

> <details>

<!-- sdn-diagram:id=baremetal_constructor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_constructor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_constructor_spec -> std
baremetal_constructor_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_constructor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Constructor Specification

## Scenarios

### Engine2D baremetal constructor

#### preserves explicit dimensions on the sized baremetal path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(8, 6)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend_dims(8, 6, backend)

expect(engine.backend_name()).to_equal("baremetal")
expect(engine.width()).to_equal(8)
expect(engine.height()).to_equal(6)
```

</details>

#### keeps the legacy baremetal constructor contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(11, 7)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend(backend)

expect(engine.backend_name()).to_equal("baremetal")
expect(engine.width()).to_equal(11)
expect(engine.height()).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D baremetal constructor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
