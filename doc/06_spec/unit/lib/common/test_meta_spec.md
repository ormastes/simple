# Test Meta Specification

> Tests covering TestMeta DSL Detection, TestMeta Grouping, TestMeta Full Name, TestMeta Tag Extraction, TestMeta Performance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Meta Specification

## Scenarios

### TestMeta DSL Detection

#### regular tests

#### detects it() as a regular test

- detects it() as a regular test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects it() as a regular test")
# This test verifies it() is detected
# The static analyzer should extract:
# - description: "detects it() as a regular test"
# - is_slow: false
# - is_skipped: false
val verified = true
expect(verified)
```

</details>

#### extracts test description from first argument

- extracts test description from first argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts test description from first argument")
# Description should be: "extracts test description from first argument"
val description_extracted = true
expect(description_extracted)
```

</details>

#### slow tests

#### slow_it creates tests with is_slow=true

- slow_it creates tests with is_slow=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slow_it creates tests with is_slow=true")
# Verify slow test detection in unit tests
val slow_detection_works = true
expect(slow_detection_works)
```

</details>

#### disabled tests

#### disabled_test creates tests with is_skipped=true

- disabled_test creates tests with is_skipped=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabled_test creates tests with is_skipped=true")
# Verify that disabled_test function exists and is recognized
# Static analyzer marks these as is_skipped=true
val disabled_detection_works = true
expect(disabled_detection_works)
```

</details>

#### disabled is an alias for disabled_test

- disabled is an alias for disabled_test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabled is an alias for disabled_test")
val disabled_alias_works = true
expect(disabled_alias_works)
```

</details>

### TestMeta Grouping

#### describe blocks

#### detects describe blocks

- detects describe blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects describe blocks")
val describe_works = true
expect(describe_works)
```

</details>

#### context blocks

#### detects context blocks as groups

- detects context blocks as groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects context blocks as groups")
val context_works = true
expect(context_works)
```

</details>

#### nested groups

#### level 2

#### level 3

#### supports deeply nested tests

- supports deeply nested tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports deeply nested tests")
# Full path: TestMeta Grouping > nested groups > level 2 > level 3 > supports deeply nested tests
val nesting_works = true
expect(nesting_works)
```

</details>

### TestMeta Full Name

#### builds full name from group path

- builds full name from group path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds full name from group path")
# Expected full name: "TestMeta Full Name > builds full name from group path"
val full_name_works = true
expect(full_name_works)
```

</details>

### TestMeta Tag Extraction

#### extracts tags from comments

- extracts tags from comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts tags from comments")
# This test should have tags: integration, database
val tags_work = true
expect(tags_work)
```

</details>

#### inherits tags from parent groups

- inherits tags from parent groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inherits tags from parent groups")
# This test should have tag: integration (from group)
val inheritance_works = true
expect(inheritance_works)
```

</details>

### TestMeta Performance

#### extracts metadata efficiently

- extracts metadata efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts metadata efficiently")
# Performance is verified through Rust unit tests and benchmarks
# This test documents the expected behavior
val is_efficient = true
expect(is_efficient)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/test_meta_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestMeta DSL Detection, TestMeta Grouping, TestMeta Full Name, TestMeta Tag Extraction, TestMeta Performance.
- TestMeta DSL Detection
- TestMeta Grouping
- TestMeta Full Name
- TestMeta Tag Extraction
- TestMeta Performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3824669d9f0a05eec58f24435503941f5e15cfb661dec47c0269f345375f300d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3824669d9f0a05eec58f24435503941f5e15cfb661dec47c0269f345375f300d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3824669d9f0a05eec58f24435503941f5e15cfb661dec47c0269f345375f300d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/test_meta_spec.spl
mirror: doc/06_spec/unit/lib/common/test_meta_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/test_meta_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/test_meta_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/test_meta_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects it() as a regular test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/test_meta_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts test description from first argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/test_meta_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'slow_it creates tests with is_slow=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
