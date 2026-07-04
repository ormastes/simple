# Threshold System Specification

> <details>

<!-- sdn-diagram:id=threshold_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=threshold_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

threshold_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=threshold_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Threshold System Specification

## Scenarios

### Threshold Types

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = threshold_config_default()
expect(config.default_threshold).to_equal(70)
expect(config.enforce).to_equal(false)
expect(config.fail_on_below).to_equal(false)
expect(config.scope_names.len()).to_equal(0)
```

</details>

#### gets scope threshold with match

1. var config = threshold config default
   - Expected: threshold equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = threshold_config_default()
config.scope_names = ["src/std/"]
config.scope_values = [90]

val threshold = threshold_config_get(config, "src/std/string.spl")
expect(threshold).to_equal(90)
```

</details>

#### gets default threshold when no match

1. var config = threshold config default
   - Expected: threshold equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = threshold_config_default()
config.default_threshold = 75
config.scope_names = ["src/std/"]
config.scope_values = [90]

val threshold = threshold_config_get(config, "src/core/lexer.spl")
expect(threshold).to_equal(75)
```

</details>

#### creates scope coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov = scope_coverage_create("src/std/", 80, 100, 85, [])
expect(cov.scope).to_equal("src/std/")
expect(cov.threshold).to_equal(80)
expect(cov.actual).to_equal(85)
expect(cov.passed).to_equal(true)
expect(cov.total_items).to_equal(100)
expect(cov.covered_items).to_equal(85)
```

</details>

#### marks failed coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov = scope_coverage_create("src/app/", 70, 100, 60, [])
expect(cov.actual).to_equal(60)
expect(cov.passed).to_equal(false)
```

</details>

### Config Parser

#### parses default config when file missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_threshold_config("nonexistent.sdn")
expect(config.default_threshold).to_equal(70)
```

</details>

#### parses basic config

1. file write
   - Expected: config.default_threshold equals `85`
   - Expected: config.enforce is true
   - Expected: config.fail_on_below is true
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "doc_coverage {\n    default_threshold 85\n    enforce true\n    fail_on_below_threshold true\n}"
file_write("test_threshold.sdn", content)

val config = parse_threshold_config("test_threshold.sdn")
expect(config.default_threshold).to_equal(85)
expect(config.enforce).to_equal(true)
expect(config.fail_on_below).to_equal(true)

file_delete("test_threshold.sdn")
```

</details>

#### parses thresholds section

1. file write
   - Expected: config.scope_names.len() equals `2`
   - Expected: config.scope_names[0] equals `src/std/`
   - Expected: config.scope_values[0] equals `90`
   - Expected: config.scope_names[1] equals `src/core/`
   - Expected: config.scope_values[1] equals `75`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "doc_coverage {\n    thresholds {\n        \"src/std/\" 90\n        \"src/core/\" 75\n    }\n}"
file_write("test_threshold2.sdn", content)

val config = parse_threshold_config("test_threshold2.sdn")
expect(config.scope_names.len()).to_equal(2)
expect(config.scope_names[0]).to_equal("src/std/")
expect(config.scope_values[0]).to_equal(90)
expect(config.scope_names[1]).to_equal("src/core/")
expect(config.scope_values[1]).to_equal(75)

file_delete("test_threshold2.sdn")
```

</details>

#### parses exclusions

1. file write
   - Expected: config.exclusions.len() equals `2`
   - Expected: config.exclusions[0] equals `test/**`
   - Expected: config.exclusions[1] equals `examples/**`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "doc_coverage {\n    exclude [\n        \"test/**\"\n        \"examples/**\"\n    ]\n}"
file_write("test_threshold3.sdn", content)

val config = parse_threshold_config("test_threshold3.sdn")
expect(config.exclusions.len()).to_equal(2)
expect(config.exclusions[0]).to_equal("test/**")
expect(config.exclusions[1]).to_equal("examples/**")

file_delete("test_threshold3.sdn")
```

</details>

### Coverage Calculator

#### calculates coverage for single scope

1. var config = threshold config default
   - Expected: results.len() equals `1`
   - Expected: cov.scope equals `src/std/`
   - Expected: cov.total_items equals `3`
   - Expected: cov.covered_items equals `2`
   - Expected: cov.actual equals `66`
   - Expected: cov.passed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = threshold_config_default()
config.scope_names = ["src/std/"]
config.scope_values = [80]

val all_files = ["src/std/string.spl", "src/std/array.spl", "src/std/math.spl"]
val covered = ["src/std/string.spl", "src/std/array.spl"]

val results = calculate_scope_coverage(all_files, covered, config)
expect(results.len()).to_equal(1)

val cov = results[0]
expect(cov.scope).to_equal("src/std/")
expect(cov.total_items).to_equal(3)
expect(cov.covered_items).to_equal(2)
expect(cov.actual).to_equal(66)
expect(cov.passed).to_equal(false)
```

</details>

#### calculates coverage for multiple scopes

1. var config = threshold config default
   - Expected: results.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = threshold_config_default()
config.scope_names = ["src/std/", "src/core/"]
config.scope_values = [80, 70]

val all_files = [
    "src/std/string.spl",
    "src/std/array.spl",
    "src/core/lexer.spl",
    "src/core/parser.spl"
]
val covered = [
    "src/std/string.spl",
    "src/std/array.spl",
    "src/core/lexer.spl"
]

val results = calculate_scope_coverage(all_files, covered, config)
expect(results.len()).to_equal(2)
```

</details>

#### tracks missing items

1. var config = threshold config default
   - Expected: cov.missing_items.len() equals `2`
   - Expected: cov.missing_items[0] equals `src/std/b.spl`
   - Expected: cov.missing_items[1] equals `src/std/c.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = threshold_config_default()
val all_files = ["src/std/a.spl", "src/std/b.spl", "src/std/c.spl"]
val covered = ["src/std/a.spl"]

val results = calculate_scope_coverage(all_files, covered, config)
val cov = results[0]
expect(cov.missing_items.len()).to_equal(2)
expect(cov.missing_items[0]).to_equal("src/std/b.spl")
expect(cov.missing_items[1]).to_equal("src/std/c.spl")
```

</details>

### Threshold Validator

#### validates all passing thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov1 = scope_coverage_create("src/std/", 80, 100, 85, [])
val cov2 = scope_coverage_create("src/core/", 70, 100, 75, [])
val coverages = [cov1, cov2]

val result = validate_thresholds(coverages)
val all_passed = result.0
val failed = result.1

expect(all_passed).to_equal(true)
expect(failed.len()).to_equal(0)
```

</details>

#### validates with failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov1 = scope_coverage_create("src/std/", 80, 100, 85, [])
val cov2 = scope_coverage_create("src/app/", 70, 100, 60, [])
val coverages = [cov1, cov2]

val result = validate_thresholds(coverages)
val all_passed = result.0
val failed = result.1

expect(all_passed).to_equal(false)
expect(failed.len()).to_equal(1)
expect(failed[0]).to_equal("src/app/")
```

</details>

#### generates threshold report

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov1 = scope_coverage_create("src/std/", 80, 100, 85, [])
val cov2 = scope_coverage_create("src/app/", 70, 100, 60, ["src/app/a.spl"])
val coverages = [cov1, cov2]

val result = validate_thresholds(coverages)
val all_passed = result.0
val failed = result.1

val report = generate_threshold_report(coverages, all_passed, failed)
expect(report.contains("Doc Coverage Threshold Report")).to_equal(true)
expect(report.contains("PASS")).to_equal(true)
expect(report.contains("FAIL")).to_equal(true)
expect(report.contains("src/app/a.spl")).to_equal(true)
```

</details>

#### calculates overall coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cov1 = scope_coverage_create("src/std/", 80, 100, 80, [])
val cov2 = scope_coverage_create("src/core/", 70, 50, 40, [])
val coverages = [cov1, cov2]

val overall = get_overall_coverage(coverages)
expect(overall).to_equal(80)
```

</details>

#### handles zero total items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coverages = []
val overall = get_overall_coverage(coverages)
expect(overall).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/threshold_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Threshold Types
- Config Parser
- Coverage Calculator
- Threshold Validator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
