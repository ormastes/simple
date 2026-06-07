# Mdsoc Stats Specification

> <details>

<!-- sdn-diagram:id=mdsoc_stats_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mdsoc_stats_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mdsoc_stats_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mdsoc_stats_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mdsoc Stats Specification

## Scenarios

### MDSOC Coverage Statistics

#### calculates coverage for Public exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["sort", "map", "filter"]
val documented = ["sort", "map"]
val violations = ["filter: missing documentation"]

val stats = calculate_mdsoc_coverage(
    "array_capsule",
    public_exports,
    documented,
    violations
)

expect(stats.capsule_name).to_equal("array_capsule")
expect(stats.total_public_exports).to_equal(3)
expect(stats.documented_public_exports).to_equal(2)
expect(stats.undocumented_public_exports).to_equal(1)

# Coverage should be 66.6% (2/3)
expect(stats.coverage_percentage).to_be_greater_than(66.0)
expect(stats.coverage_percentage).to_be_less_than(67.0)
```

</details>

#### handles 100% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["sort", "map"]
val documented = ["sort", "map"]
val violations: [text] = []

val stats = calculate_mdsoc_coverage(
    "perfect_capsule",
    public_exports,
    documented,
    violations
)

expect(stats.coverage_percentage).to_equal(100.0)
expect(stats.undocumented_public_exports).to_equal(0)
expect(stats.doc_violations.len()).to_equal(0)
```

</details>

#### handles 0% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["sort", "map", "filter"]
val documented: [text] = []
val violations = [
    "sort: missing documentation",
    "map: missing documentation",
    "filter: missing documentation"
]

val stats = calculate_mdsoc_coverage(
    "bad_capsule",
    public_exports,
    documented,
    violations
)

expect(stats.coverage_percentage).to_equal(0.0)
expect(stats.undocumented_public_exports).to_equal(3)
expect(stats.doc_violations.len()).to_equal(3)
```

</details>

#### handles empty capsule

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports: [text] = []
val documented: [text] = []
val violations: [text] = []

val stats = calculate_mdsoc_coverage(
    "empty_capsule",
    public_exports,
    documented,
    violations
)

expect(stats.total_public_exports).to_equal(0)
expect(stats.coverage_percentage).to_equal(0.0)
```

</details>

#### formats MDSOC report

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["sort", "map"]
val documented = ["sort"]
val violations = ["map: missing documentation at src/array/mod.spl:42"]

val stats = calculate_mdsoc_coverage(
    "array_capsule",
    public_exports,
    documented,
    violations
)

val report = format_mdsoc_report(stats)

expect(report).to_contain("array_capsule")
expect(report).to_contain("Public exports:")
expect(report).to_contain("2")
expect(report).to_contain("Documented:")
expect(report).to_contain("1")
expect(report).to_contain("Undocumented:")
expect(report).to_contain("1")
expect(report).to_contain("Documentation Violations:")
expect(report).to_contain("map: missing documentation")
```

</details>

#### converts MDSOC stats to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["sort"]
val documented = ["sort"]
val violations: [text] = []

val stats = calculate_mdsoc_coverage(
    "test_capsule",
    public_exports,
    documented,
    violations
)

val json = mdsoc_stats_to_json(stats)

expect(json).to_contain("capsule_name")
expect(json).to_contain("test_capsule")
expect(json).to_contain("total_public_exports")
expect(json).to_contain("1")
expect(json).to_contain("coverage_percentage")
expect(json).to_contain("100")
expect(json).to_contain("violations")
```

</details>

#### includes violations in JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_exports = ["a", "b"]
val documented: [text] = []
val violations = ["a: missing docs", "b: missing docs"]

val stats = calculate_mdsoc_coverage(
    "test",
    public_exports,
    documented,
    violations
)

val json = mdsoc_stats_to_json(stats)

expect(json).to_contain("a: missing docs")
expect(json).to_contain("b: missing docs")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc/public_check/mdsoc_stats_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MDSOC Coverage Statistics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
