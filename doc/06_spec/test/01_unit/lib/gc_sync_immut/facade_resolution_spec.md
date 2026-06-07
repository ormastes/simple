# Facade Resolution Specification

> <details>

<!-- sdn-diagram:id=facade_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=facade_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

facade_resolution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=facade_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facade Resolution Specification

## Scenarios

### gc_sync_immut facade resolution

#### resolves persistent helpers through the GC async immutable facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pfilter([1, 2, 3, 4], _1 > 2)).to_equal([3, 4])
expect(nogc_async_immut_version()).to_equal("0.1.0")
```

</details>

#### preserves root coordination type behavior through the sync GC facade

1. var atom = Atom new
2. atom reset
   - Expected: atom.deref() equals `12`
3. var snapshot = VersionedSnapshot new
4. snapshot update
   - Expected: snapshot.current() equals `right`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atom = Atom.new(11)
atom.reset(12)
expect(atom.deref()).to_equal(12)

var snapshot = VersionedSnapshot.new("left")
snapshot.update("right")
expect(snapshot.current()).to_equal("right")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_immut/facade_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_sync_immut facade resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
