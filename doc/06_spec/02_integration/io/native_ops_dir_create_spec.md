# Native directory create operations

> Verifies the native directory API can create and remove a temporary directory through the Simple directory facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native directory create operations

Verifies the native directory API can create and remove a temporary directory through the Simple directory facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_dir_create_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Native directory create operations

## Overview

Verifies the native directory API can create and remove a temporary directory
through the Simple directory facade.

## Acceptance

- A temporary directory can be created.
- The directory is detected as a directory.
- The directory tree can be removed.

## Scenarios

### Native Directory Ops

<details>
<summary>Advanced: creates directories</summary>

#### creates directories _(slow)_

- Verify: creates directories


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-IO_NATIVE_OPS_DIR_CREATE-001
step("Verify: creates directories")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val test_dir = "{tmp}/simple_native_dir_test"

check(dir_create(test_dir, false))
check(is_dir(test_dir))
check(dir_remove_all(test_dir) == 0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6cb2476df5826d38d8721f6522ec12b8e5f94dec2799155addc4d31837354bf7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cb2476df5826d38d8721f6522ec12b8e5f94dec2799155addc4d31837354bf7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cb2476df5826d38d8721f6522ec12b8e5f94dec2799155addc4d31837354bf7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/io/native_ops_dir_create_spec.spl
mirror: doc/06_spec/02_integration/io/native_ops_dir_create_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/io/native_ops_dir_create_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/io/native_ops_dir_create_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/io/native_ops_dir_create_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
