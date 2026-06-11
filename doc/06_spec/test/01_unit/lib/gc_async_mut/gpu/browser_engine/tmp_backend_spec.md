# Tmp Backend Specification

> <details>

<!-- sdn-diagram:id=tmp_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Backend Specification

## Scenarios

### backend name debug

#### software backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = BrowserRenderer.create_with_backend(10, 10, "software")
expect(r.backend_name()).to_equal("software")
```

</details>

#### cpu backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = BrowserRenderer.create_with_backend(10, 10, "cpu")
expect(r.backend_name()).to_equal("cpu")
```

</details>

#### metal backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = BrowserRenderer.create_with_backend(10, 10, "metal")
expect(r.backend_name()).to_equal("metal")
```

</details>

#### unknown backend falls back to software

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = BrowserRenderer.create_with_backend(10, 10, "unknown_xyz")
expect(r.backend_name()).to_equal("software")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- backend name debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
