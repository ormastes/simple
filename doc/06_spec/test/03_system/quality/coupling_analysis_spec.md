# Coupling Analysis Specification

> <details>

<!-- sdn-diagram:id=coupling_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coupling_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coupling_analysis_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coupling_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Analysis Specification

## Scenarios

### Coupling Analysis

### CBO / Fan-in / Fan-out / Instability

#### computes fan-out as count of distinct module dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes fan-in as count of modules depending on this module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes instability as fan_out / (fan_in + fan_out)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### handles zero fan-in and fan-out gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### SCC Cycle Detection

#### detects circular dependencies using SCC

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### does not report single-node SCCs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### finds all SCCs in a complex graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Layer Violations

#### flags backward dependencies between numbered compiler layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### allows forward dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### extracts layer numbers from compiler paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### DSM Matrix

<details>
<summary>Advanced: builds NxN matrix with dependency counts</summary>

#### builds NxN matrix with dependency counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>


</details>

### Output Formats

#### produces text format report

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### produces JSON format report

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### produces Markdown format report

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Coupling Lint Rules

#### W0501 flags high CBO

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0502 flags circular dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0503 flags layer violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0504 flags instability inversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### LCOM4 Cohesion

#### computes LCOM4 = 1 for cohesive class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes LCOM4 > 1 for uncohesive class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Public API Quality

#### computes PSS as public methods + public fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes EUR as externally used / total public

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes normalized entropy for usage distribution

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Argument Signature Similarity

#### detects exact type-set duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### detects near-duplicates with edit distance 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### computes correct edit distance for different type sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Relaxed Token Duplication

#### matches token-kind-only sequences ignoring variable names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

### Extended Lint Rules

#### W0505 flags high LCOM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0506 flags high public surface ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0507 flags dead public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

#### W0508 flags high API complexity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pass_do_nothing
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/coupling_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Coupling Analysis
- CBO / Fan-in / Fan-out / Instability
- SCC Cycle Detection
- Layer Violations
- DSM Matrix
- Output Formats
- Coupling Lint Rules
- LCOM4 Cohesion
- Public API Quality
- Argument Signature Similarity
- Relaxed Token Duplication
- Extended Lint Rules

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
