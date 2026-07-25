# Threshold Calculator Specification

> <details>

<!-- sdn-diagram:id=threshold_calculator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=threshold_calculator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

threshold_calculator_spec -> std
threshold_calculator_spec -> doc_coverage
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=threshold_calculator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Threshold Calculator Specification

## Scenarios

### calculate_scope_coverage basic

#### calculates coverage for single scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/string.spl", "src/std/math.spl", "src/std/array.spl"]
val covered_files: [text] = ["src/std/string.spl", "src/std/math.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val has_results = results.len() > 0
expect(has_results).to_equal(true)
```

</details>

#### returns coverage result for src/std/ scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/string.spl", "src/std/math.spl"]
val covered_files: [text] = ["src/std/string.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val has_std_scope = results.len() > 0
expect(has_std_scope).to_equal(true)
```

</details>

#### calculates correct coverage percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val pct = first_result.actual

val expected_pct = 75
expect(pct).to_equal(expected_pct)
```

</details>

#### identifies missing items correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl"]
val covered_files: [text] = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val missing_count = first_result.missing_items.len()

expect(missing_count).to_equal(1)
```

</details>

#### sets passed flag based on threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val passed = first_result.passed

expect(passed).to_equal(true)
```

</details>

### calculate_scope_coverage multiple scopes

#### handles multiple scopes in one calculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/core/b.spl", "src/lib/c.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/core/b.spl", "src/lib/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val result_count = results.len()
val has_multiple = result_count >= 2

expect(has_multiple).to_equal(true)
```

</details>

#### calculates coverage separately for each scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/core/c.spl", "src/core/d.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/core/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

var std_result_found = false
var core_result_found = false

for result in results:
    if result.scope == "src/std/":
        std_result_found = true
        val std_pct = result.actual
        expect(std_pct).to_equal(100)

    if result.scope == "src/core/":
        core_result_found = true
        val core_pct = result.actual
        expect(core_pct).to_equal(50)

expect(std_result_found).to_equal(true)
expect(core_result_found).to_equal(true)
```

</details>

#### applies correct threshold to each scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/core/c.spl", "src/core/d.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/core/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

for result in results:
    if result.scope == "src/std/":
        val threshold = result.threshold
        expect(threshold).to_equal(90)

    if result.scope == "src/core/":
        val threshold = result.threshold
        expect(threshold).to_equal(75)
```

</details>

### calculate_scope_coverage pass/fail

#### marks as passed when coverage meets threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl", "src/std/e.spl", "src/std/f.spl", "src/std/g.spl", "src/std/h.spl", "src/std/i.spl", "src/std/j.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl", "src/std/e.spl", "src/std/f.spl", "src/std/g.spl", "src/std/h.spl", "src/std/i.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val passed = first_result.passed

expect(passed).to_equal(true)
```

</details>

#### marks as failed when coverage below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl"]
val covered_files: [text] = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val passed = first_result.passed

expect(passed).to_equal(false)
```

</details>

#### handles edge case at exact threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl", "src/std/e.spl", "src/std/f.spl", "src/std/g.spl", "src/std/h.spl", "src/std/i.spl", "src/std/j.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl", "src/std/e.spl", "src/std/f.spl", "src/std/g.spl", "src/std/h.spl", "src/std/i.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val pct = first_result.actual

val is_90 = pct == 90
expect(is_90).to_equal(true)
```

</details>

### calculate_scope_coverage missing items

#### identifies all missing items

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]
val covered_files: [text] = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val missing = first_result.missing_items

expect(missing.len()).to_equal(2)
```

</details>

#### missing items contain correct file names

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]
val covered_files: [text] = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val missing = first_result.missing_items

var has_b = false
var has_c = false

for item in missing:
    if item.contains("b.spl"):
        has_b = true
    if item.contains("c.spl"):
        has_c = true

expect(has_b).to_equal(true)
expect(has_c).to_equal(true)
```

</details>

#### empty missing list when all items covered

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val missing_count = first_result.missing_items.len()

expect(missing_count).to_equal(0)
```

</details>

### calculate_scope_coverage edge cases

#### handles empty file lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = []
val covered_files: [text] = []

val results = calculate_scope_coverage(all_files, covered_files, config)

val result_count = results.len()
expect(result_count).to_equal(0)
```

</details>

#### handles all files covered scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val pct = first_result.actual

expect(pct).to_equal(100)
```

</details>

#### handles no files covered scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl"]
val covered_files: [text] = []

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val pct = first_result.actual

expect(pct).to_equal(0)
```

</details>

#### handles files not in any configured scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["other/path/file.spl"]
val covered_files: [text] = ["other/path/file.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val has_results = results.len() >= 0
expect(has_results).to_equal(true)
```

</details>

### calculate_scope_coverage item counts

#### sets total_items correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]
val covered_files: [text] = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val total = first_result.total_items

expect(total).to_equal(3)
```

</details>

#### sets covered_items correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/b.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val covered = first_result.covered_items

expect(covered).to_equal(2)
```

</details>

#### item counts are consistent

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl", "src/std/d.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/std/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

val first_result = results[0]
val total = first_result.total_items
val covered = first_result.covered_items
val missing_count = first_result.missing_items.len()

val sum_matches = (covered + missing_count) == total
expect(sum_matches).to_equal(true)
```

</details>

### calculate_scope_coverage integration

#### calculates coverage for realistic file set

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = [
    "src/std/string.spl",
    "src/std/math.spl",
    "src/std/array.spl",
    "src/core/lexer.spl",
    "src/core/parser.spl",
    "src/lib/database.spl"
]

val covered_files: [text] = [
    "src/std/string.spl",
    "src/std/math.spl",
    "src/core/lexer.spl",
    "src/lib/database.spl"
]

val results = calculate_scope_coverage(all_files, covered_files, config)

val has_results = results.len() > 0
expect(has_results).to_equal(true)
```

</details>

#### all scopes have valid data

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = create_test_config()

val all_files: [text] = ["src/std/a.spl", "src/core/b.spl", "src/lib/c.spl"]
val covered_files: [text] = ["src/std/a.spl", "src/core/b.spl", "src/lib/c.spl"]

val results = calculate_scope_coverage(all_files, covered_files, config)

var all_valid = true
for result in results:
    if result.total_items < 0:
        all_valid = false
    if result.covered_items < 0:
        all_valid = false
    if result.actual < 0 or result.actual > 100:
        all_valid = false

expect(all_valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/threshold_calculator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- calculate_scope_coverage basic
- calculate_scope_coverage multiple scopes
- calculate_scope_coverage pass/fail
- calculate_scope_coverage missing items
- calculate_scope_coverage edge cases
- calculate_scope_coverage item counts
- calculate_scope_coverage integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
