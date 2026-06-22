# Register T32 Gdb Specification

> <details>

<!-- sdn-diagram:id=register_t32_gdb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=register_t32_gdb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

register_t32_gdb_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=register_t32_gdb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Register T32 Gdb Specification

## Scenarios

### T32 GDB feature registration

#### registers execution control at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
expect(features[0].name).to_equal("Halt")
expect(features[0].rank).to_equal(0)
```

</details>

#### registers TraceCapture at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
expect(features[7].name).to_equal("TraceCapture")
expect(features[7].rank).to_equal(0)
```

</details>

#### registers CoverageCollect at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
expect(features[8].name).to_equal("CoverageCollect")
expect(features[8].rank).to_equal(0)
```

</details>

#### registers PracticeScript at rank NATIVE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
expect(features[9].name).to_equal("PracticeScript")
expect(features[9].rank).to_equal(0)
```

</details>

#### all features use t32-gdb backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
for f in features:
    expect(f.backend).to_equal("t32-gdb")
```

</details>

#### has 10 registered features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = t32gdb_registered_features()
expect(features.len()).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/register_t32_gdb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 GDB feature registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
