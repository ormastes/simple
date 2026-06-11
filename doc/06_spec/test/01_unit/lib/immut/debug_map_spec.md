# Debug Map Specification

> <details>

<!-- sdn-diagram:id=debug_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_map_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Map Specification

## Scenarios

### Debug VersionedSnapshot

#### snapshot get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
val snap = vs.snapshot()
expect(snap.get()).to_equal(42)
```

</details>

#### snapshot get_version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
val snap = vs.snapshot()
expect(snap.get_version()).to_equal(0)
```

</details>

#### snapshot version field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
val snap = vs.snapshot()
expect(snap.version).to_equal(0)
```

</details>

#### direct snapshot new

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = Snapshot(version: 0, value: 42)
expect(snap.get()).to_equal(42)
expect(snap.get_version()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/debug_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Debug VersionedSnapshot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
