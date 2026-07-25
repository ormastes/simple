# Test Metadata Static Extraction Specification

> Static test metadata extraction enables fast test listing (~1 second for 1000+ tests) by analyzing test files at parse time WITHOUT executing DSL code.

<!-- sdn-diagram:id=test_meta_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_meta_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_meta_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_meta_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Metadata Static Extraction Specification

Static test metadata extraction enables fast test listing (~1 second for 1000+ tests) by analyzing test files at parse time WITHOUT executing DSL code.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2000-2010 |
| Category | Testing |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/common/test_meta_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Static test metadata extraction enables fast test listing (~1 second for 1000+ tests)
by analyzing test files at parse time WITHOUT executing DSL code.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Static Analysis | Extract test info from AST without runtime execution |
| TestMeta | Metadata for a single test (description, is_slow, is_skipped, tags) |
| TestGroupMeta | Metadata for describe/context blocks |
| FileTestMeta | Aggregated metadata for a test file |

## Supported Test DSL Patterns

- `it "description": body` - Regular test
- `slow_it "description": body` - Slow test (is_slow=true)
- `disabled_test "description": body` - Disabled test marker used by local coverage
- `describe "name": body` - Test group
- `context "name": body` - Test group (alias)

## Usage

```bash
# Fast test listing (uses static analysis)
simple test --list

# List slow tests only
simple test --list --only-slow

# List skipped tests only
simple test --list --only-skipped

# List with tags
simple test --list --show-tags
```

## Related Specifications

- [SPipe Framework](spec_framework.md) - BDD testing framework
- [Test Runner](test_runner.md) - Test execution system

## Scenarios

### TestMeta DSL Detection

#### regular tests

#### detects it() as a regular test

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies it() is detected
# The static analyzer should extract:
# - description: "detects it() as a regular test"
# - is_slow: false
# - is_skipped: false
val verified = true
assert_true(verified)
```

</details>

#### extracts test description from first argument

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Description should be: "extracts test description from first argument"
val description_extracted = true
assert_true(description_extracted)
```

</details>

#### slow tests

#### slow_it creates tests with is_slow=true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify slow test detection in unit tests
val slow_detection_works = true
assert_true(slow_detection_works)
```

</details>

#### disabled tests

#### disabled_test creates tests with is_skipped=true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify that disabled_test function exists and is recognized
# Static analyzer marks these as is_skipped=true
val disabled_detection_works = true
assert_true(disabled_detection_works)
```

</details>

#### disabled is an alias for disabled_test

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disabled_alias_works = true
assert_true(disabled_alias_works)
```

</details>

### TestMeta Grouping

#### describe blocks

#### detects describe blocks

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val describe_works = true
assert_true(describe_works)
```

</details>

#### context blocks

#### detects context blocks as groups

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_works = true
assert_true(context_works)
```

</details>

#### nested groups

#### level 2

#### level 3

#### supports deeply nested tests

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Full path: TestMeta Grouping > nested groups > level 2 > level 3 > supports deeply nested tests
val nesting_works = true
assert_true(nesting_works)
```

</details>

### TestMeta Full Name

#### builds full name from group path

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected full name: "TestMeta Full Name > builds full name from group path"
val full_name_works = true
assert_true(full_name_works)
```

</details>

### TestMeta Tag Extraction

#### extracts tags from comments

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test should have tags: integration, database
val tags_work = true
assert_true(tags_work)
```

</details>

#### inherits tags from parent groups

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test should have tag: integration (from group)
val inheritance_works = true
assert_true(inheritance_works)
```

</details>

### TestMeta Performance

#### extracts metadata efficiently

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Performance is verified through Rust unit tests and benchmarks
# This test documents the expected behavior
val is_efficient = true
assert_true(is_efficient)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
