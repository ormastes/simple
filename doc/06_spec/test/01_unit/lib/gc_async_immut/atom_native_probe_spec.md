# Atom Native Probe Specification

> 1. var atom = Atom new

<!-- sdn-diagram:id=atom_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atom_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atom_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atom_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atom Native Probe Specification

## Scenarios

### gc_async_immut atom native probe

#### constructs an atom

1. var atom = Atom new
2. expect atom deref


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atom = Atom.new(5)
expect atom.deref() == 5
```

</details>

#### resets an atom

1. var atom = Atom new
2. atom reset
3. expect atom deref


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atom = Atom.new(5)
atom.reset(8)
expect atom.deref() == 8
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/atom_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut atom native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
