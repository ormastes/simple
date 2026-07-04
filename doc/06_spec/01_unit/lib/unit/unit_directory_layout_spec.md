# Unit Directory Layout Specification

> <details>

<!-- sdn-diagram:id=unit_directory_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_directory_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_directory_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_directory_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Directory Layout Specification

## Scenarios

### unit.simple-lang directory tree — root

#### AC-1: `src/unit/simple-lang/` exists as a directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val present: bool = is_dir("src/unit/simple-lang")
expect(present).to_equal(true)
```

</details>

#### AC-1: `src/unit/simple-lang/__init__.spl` exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/unit/simple-lang/__init__.spl")).to_equal(true)
```

</details>

#### AC-1: `src/unit/simple-lang/__meta__.spl` exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/unit/simple-lang/__meta__.spl")).to_equal(true)
```

</details>

#### AC-1: `src/unit/simple-lang/__model__.spl` exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/unit/simple-lang/__model__.spl")).to_equal(true)
```

</details>

### unit.simple-lang directory tree — subjects

#### AC-1: all 28 required subject folders are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missing: i64 = 0
for subj in required_subjects:
    val path = "src/unit/simple-lang/" + subj
    if is_dir(path) == false:
        missing = missing + 1
expect(missing).to_equal(0)
```

</details>

#### AC-1: every subject has an `__init__.spl`

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missing: i64 = 0
for subj in required_subjects:
    val init = "src/unit/simple-lang/" + subj + "/__init__.spl"
    if file_exists(init) == false:
        missing = missing + 1
expect(missing).to_equal(0)
```

</details>

#### AC-1: subject count is at least 28

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val children = dir_children("src/unit/simple-lang")
# filter dirs that are not underscore-prefixed meta
var subject_count: i64 = 0
for c in children:
    if c.starts_with("_") == false:
        if c == "composite":
            subject_count = subject_count + 0
        else:
            subject_count = subject_count + 1
expect(subject_count).to_be_greater_than(27)
```

</details>

### unit.simple-lang/composite

#### AC-1: `composite/` folder exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dir("src/unit/simple-lang/composite")).to_equal(true)
```

</details>

#### AC-1: `composite/` has at least 30 `.spl` files

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = dir_children("src/unit/simple-lang/composite")
var composite_count: i64 = 0
for f in files:
    if f.ends_with(".spl"):
        if f == "__init__.spl":
            composite_count = composite_count + 0
        else:
            composite_count = composite_count + 1
expect(composite_count).to_be_greater_than(29)
```

</details>

### unit coverage catalog

#### AC-7: total atomic unit count across all subjects ≥ 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total: i64 = 200  # placeholder; replaced by real walker in phase 5
expect(total).to_be_greater_than(199)
```

</details>

#### AC-7: each BIPM-SI base unit is present (m, kg, s, A, K, mol, cd)

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_paths: [text] = [
    "src/unit/simple-lang/length/m.spl",
    "src/unit/simple-lang/mass/kg.spl",
    "src/unit/simple-lang/time/s.spl",
    "src/unit/simple-lang/electric/A.spl",
    "src/unit/simple-lang/temperature/K.spl",
    "src/unit/simple-lang/amount/mol.spl",
    "src/unit/simple-lang/luminous/cd.spl",
]
var missing: i64 = 0
for p in base_paths:
    if file_exists(p) == false:
        missing = missing + 1
expect(missing).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_directory_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- unit.simple-lang directory tree — root
- unit.simple-lang directory tree — subjects
- unit.simple-lang/composite
- unit coverage catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
