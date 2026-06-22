# Feature Ids Specification

> <details>

<!-- sdn-diagram:id=feature_ids_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_ids_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_ids_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_ids_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Ids Specification

## Scenarios

### FeatureId new variants to_string

#### PracticeScript has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.PracticeScript
expect(f.to_string()).to_equal("PracticeScript")
```

</details>

#### OpenocdMonitor has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.OpenocdMonitor
expect(f.to_string()).to_equal("OpenocdMonitor")
```

</details>

#### SemihostRead has correct to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FeatureId.SemihostRead
expect(f.to_string()).to_equal("SemihostRead")
```

</details>

### FeatureId new variants distinctness

#### PracticeScript is not OpenocdMonitor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.PracticeScript
val b = FeatureId.OpenocdMonitor
expect(a.eq(b)).to_equal(false)
```

</details>

#### OpenocdMonitor is not SemihostRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.OpenocdMonitor
val b = FeatureId.SemihostRead
expect(a.eq(b)).to_equal(false)
```

</details>

#### PracticeScript equals itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.PracticeScript
val b = FeatureId.PracticeScript
expect(a.eq(b)).to_equal(true)
```

</details>

#### new variants are distinct from existing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.PracticeScript
val b = FeatureId.FlashProgram
expect(a.eq(b)).to_equal(false)
```

</details>

#### OpenocdMonitor is distinct from SystemReset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FeatureId.OpenocdMonitor
val b = FeatureId.SystemReset
expect(a.eq(b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/feature_ids_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FeatureId new variants to_string
- FeatureId new variants distinctness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
