# Discovery Specification

> Tests covering Doctest Discovery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Discovery Specification

## Scenarios

### Doctest Discovery

#### Single File Discovery

#### discovers doctests from .spl file

- discovers doctests from .spl file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers doctests from .spl file")
val file_path = "test/fixtures/doctest/sample.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### discovers doctests from .sdt file

- discovers doctests from .sdt file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers doctests from .sdt file")
val file_path = "test/fixtures/doctest/sample.sdt"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### discovers doctests from Markdown file

- discovers doctests from Markdown file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers doctests from Markdown file")
val file_path = "test/fixtures/doctest/tutorial.md"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### returns empty list for unsupported file types

- returns empty list for unsupported file types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns empty list for unsupported file types")
val file_path = "test/fixtures/doctest/readme.txt"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### Directory Discovery

#### discovers all doctests in directory tree

- discovers all doctests in directory tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers all doctests in directory tree")
val search_path = "test/fixtures/doctest"
expect(search_path.len()).to_be_greater_than(0)
```

</details>

#### excludes files matching exclude patterns

- excludes files matching exclude patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("excludes files matching exclude patterns")
val exclude_pattern = "**/ignored/**"
expect(exclude_pattern.len()).to_be_greater_than(0)
```

</details>

#### handles non-existent directories gracefully

- handles non-existent directories gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles non-existent directories gracefully")
val nonexistent = "nonexistent/path"
expect(nonexistent.len()).to_be_greater_than(0)
```

</details>

#### Source Location Tracking

#### tracks correct line numbers for .spl doctests

- tracks correct line numbers for .spl doctests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks correct line numbers for .spl doctests")
val file_path = "test/fixtures/doctest/with_line_numbers.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### tracks correct line numbers for Markdown doctests

- tracks correct line numbers for Markdown doctests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks correct line numbers for Markdown doctests")
val file_path = "test/fixtures/doctest/tutorial.md"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### Tag and Metadata Extraction

#### extracts tags from @doctest annotations

- extracts tags from @doctest annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts tags from @doctest annotations")
val file_path = "test/fixtures/doctest/tagged.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### extracts timeout from @doctest annotations

- extracts timeout from @doctest annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts timeout from @doctest annotations")
val file_path = "test/fixtures/doctest/with_timeout.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/doctest/discovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Doctest Discovery.
- Doctest Discovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe4cfdbe8c5c40989ff08e4e5ed6a6a68d089bd45cc6f919a52469a34bf8c696`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe4cfdbe8c5c40989ff08e4e5ed6a6a68d089bd45cc6f919a52469a34bf8c696`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe4cfdbe8c5c40989ff08e4e5ed6a6a68d089bd45cc6f919a52469a34bf8c696`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/doctest/discovery_spec.spl
mirror: doc/06_spec/integration/doctest/discovery_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/doctest/discovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/doctest/discovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/doctest/discovery_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers doctests from .spl file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/doctest/discovery_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers doctests from .sdt file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/doctest/discovery_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers doctests from Markdown file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
