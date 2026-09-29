# File Io Specification

> Tests covering File I/O FFI Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Io Specification

## Scenarios

### File I/O FFI Functions

#### file existence checking

#### should check if file exists

- should check if file exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should check if file exists")
# Test with a file that should exist
val exists = file.is_file("simple/std_lib/test/unit/file/file_io_spec.spl")
assert_true(exists)
```

</details>

#### should return false for non-existent files

- should return false for non-existent files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should return false for non-existent files")
val exists = file.is_file("/nonexistent/file/path/test.txt")
assert_false(exists)
```

</details>

#### file size retrieval

#### should get size of existing file

- should get size of existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should get size of existing file")
# This test file should have non-zero size
match file.size("simple/std_lib/test/unit/file/file_io_spec.spl"):
    case Ok(size):
        assert_true(size > 0)
    case Err(e):
        fail("Expected Ok, got Err: {e}")
```

</details>

#### should return error for non-existent file

- should return error for non-existent file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should return error for non-existent file")
match file.size("/nonexistent/file.txt"):
    case Ok(_):
        fail("Expected Err for non-existent file")
    case Err(_):
        pass  # Expected error
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/file/file_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering File I/O FFI Functions.
- File I/O FFI Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1804dc73ec0145266b4553d57364944d8c08ced8e95650f7679288d1d7cdae8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1804dc73ec0145266b4553d57364944d8c08ced8e95650f7679288d1d7cdae8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1804dc73ec0145266b4553d57364944d8c08ced8e95650f7679288d1d7cdae8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/std/file/file_io_spec.spl
mirror: doc/06_spec/01_unit/lib/std/file/file_io_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/file/file_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/file/file_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/file/file_io_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check if file exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/file/file_io_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should check if file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/file/file_io_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return false for non-existent files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/file/file_io_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return false for non-existent files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/file/file_io_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should get size of existing file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/file/file_io_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should get size of existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/file/file_io_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return error for non-existent file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
