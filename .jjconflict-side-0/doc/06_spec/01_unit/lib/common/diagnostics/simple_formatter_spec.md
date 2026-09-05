# Simple Formatter Specification

> Tests covering Simple Formatter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Formatter Specification

## Scenarios

### Simple Formatter

#### should define the canonical diagnostic structure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define the canonical diagnostic structure
   - Expected: src contains `struct Diagnostic`
   - Expected: src contains `severity: Severity`
   - Expected: src contains `code: text?`
   - Expected: src contains `message: text`
   - Expected: src contains `labels: [Label]`
   - Expected: src contains `notes: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define the canonical diagnostic structure")
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("struct Diagnostic")).to_equal(true)
expect(src.contains("severity: Severity")).to_equal(true)
expect(src.contains("code: text?")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("labels: [Label]")).to_equal(true)
expect(src.contains("notes: [text]")).to_equal(true)
```

</details>

#### should expose diagnostic constructors for display severities

- should expose diagnostic constructors for display severities
   - Expected: src contains `static fn error(message: text) -> Diagnostic`
   - Expected: src contains `static fn warning(message: text) -> Diagnostic`
   - Expected: src contains `static fn note(message: text) -> Diagnostic`
   - Expected: src contains `static fn help_msg(message: text) -> Diagnostic`
   - Expected: src contains `static fn info(message: text) -> Diagnostic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose diagnostic constructors for display severities")
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("static fn error(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn warning(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn note(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn help_msg(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn info(message: text) -> Diagnostic")).to_equal(true)
```

</details>

#### should support builder methods for code span labels notes and help

- should support builder methods for code span labels notes and help
   - Expected: src contains `fn with_code(code: text) -> Diagnostic`
   - Expected: src contains `fn with_span(span: Span) -> Diagnostic`
   - Expected: src contains `fn with_label(span: Span, message: text) -> Diagnostic`
   - Expected: src contains `fn with_note(note: text) -> Diagnostic`
   - Expected: src contains `fn with_help(help: text) -> Diagnostic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should support builder methods for code span labels notes and help")
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("fn with_code(code: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_span(span: Span) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_label(span: Span, message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_note(note: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_help(help: text) -> Diagnostic")).to_equal(true)
```

</details>

#### should format simple diagnostics with optional code and span

- should format simple diagnostics with optional code and span
   - Expected: src contains `fn to_string() -> text`
   - Expected: src contains `match self.code`
   - Expected: src contains `self.message`
   - Expected: src contains `fn to_string_with_span() -> text`
   - Expected: src contains `span.to_string()`
   - Expected: src contains `self.to_string()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format simple diagnostics with optional code and span")
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("fn to_string() -> text")).to_equal(true)
expect(src.contains("match self.code")).to_equal(true)
expect(src.contains("self.message")).to_equal(true)
expect(src.contains("fn to_string_with_span() -> text")).to_equal(true)
expect(src.contains("span.to_string()")).to_equal(true)
expect(src.contains("self.to_string()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Formatter.
- Simple Formatter

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

- Canonical SPipe generation for source `274bcc0d5ad9b7c3cb566c97238c4c6781a1685b300d6b090daed529f623b5e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `274bcc0d5ad9b7c3cb566c97238c4c6781a1685b300d6b090daed529f623b5e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `274bcc0d5ad9b7c3cb566c97238c4c6781a1685b300d6b090daed529f623b5e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl
mirror: doc/06_spec/01_unit/lib/common/diagnostics/simple_formatter_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/diagnostics/simple_formatter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/diagnostics/simple_formatter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define the canonical diagnostic structure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define the canonical diagnostic structure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose diagnostic constructors for display severities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose diagnostic constructors for display severities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support builder methods for code span labels notes and help' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should support builder methods for code span labels notes and help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format simple diagnostics with optional code and span' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
