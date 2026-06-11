# Nogc Async Immut Root Exports Specification

> 1. var atom = Atom new

<!-- sdn-diagram:id=nogc_async_immut_root_exports_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nogc_async_immut_root_exports_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nogc_async_immut_root_exports_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nogc_async_immut_root_exports_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nogc Async Immut Root Exports Specification

## Scenarios

### nogc_async_immut root exports

#### exports coordination types from the root module

1. var atom = Atom new
2. atom reset
   - Expected: atom.deref() equals `7`
3. var snapshot = VersionedSnapshot new
4. snapshot update
   - Expected: snapshot.current() equals `next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atom = Atom.new(5)
atom.reset(7)
expect(atom.deref()).to_equal(7)

var snapshot = VersionedSnapshot.new("start")
snapshot.update("next")
expect(snapshot.current()).to_equal("next")
```

</details>

#### exports functional helpers and version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doubled = pmap([1, 2, 3], _1 * 2)
expect(doubled).to_equal([2, 4, 6])
expect(nogc_async_immut_version()).to_equal("0.1.0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_immut_root_exports_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_immut root exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
