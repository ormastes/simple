# Diagnostics Specification

> Tests covering Position, Range, DiagnosticSeverity, Diagnostic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostics Specification

## Scenarios

### Position

#### creates position with line and character

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates position with line and character


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates position with line and character")
val pos = Position.new(10, 5)
expect pos.line == 10
expect pos.character == 5
```

</details>

#### starts at zero

- starts at zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts at zero")
val pos = Position.new(0, 0)
expect pos.line == 0
expect pos.character == 0
```

</details>

### Range

#### creates range from positions

- creates range from positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates range from positions")
val start = Position.new(0, 0)
val end = Position.new(0, 10)
val range = Range.new(start, end)
expect range.start.line == 0
expect range.end.character == 10
```

</details>

#### supports multi-line ranges

- supports multi-line ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multi-line ranges")
val start = Position.new(5, 0)
val end = Position.new(10, 20)
val range = Range.new(start, end)
expect range.start.line == 5
expect range.end.line == 10
```

</details>

### DiagnosticSeverity

#### has Error severity

- has Error severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Error severity")
expect DiagnosticSeverity.Error == DiagnosticSeverity.Error
```

</details>

#### has Warning severity

- has Warning severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Warning severity")
expect DiagnosticSeverity.Warning == DiagnosticSeverity.Warning
```

</details>

#### has Information severity

- has Information severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Information severity")
expect DiagnosticSeverity.Information == DiagnosticSeverity.Information
```

</details>

#### has Hint severity

- has Hint severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Hint severity")
expect DiagnosticSeverity.Hint == DiagnosticSeverity.Hint
```

</details>

### Diagnostic

#### creates diagnostic with range and message

- creates diagnostic with range and message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates diagnostic with range and message")
val range = Range.new(Position.new(0, 0), Position.new(0, 5))
val diag = Diagnostic.new(range, DiagnosticSeverity.Error, "Syntax error")
expect diag.message == "Syntax error"
expect diag.severity == DiagnosticSeverity.Error
```

</details>

#### adds source

- adds source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds source")
val range = Range.new(Position.new(0, 0), Position.new(0, 5))
val diag = Diagnostic.new(range, DiagnosticSeverity.Warning, "Unused variable")
    .with_source("simple-lint")
expect diag.source != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/diagnostics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Position, Range, DiagnosticSeverity, Diagnostic.
- Position
- Range
- DiagnosticSeverity
- Diagnostic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `d358d8a74bdba2fdc60d68954453d6af07570787f99fc70714b79be8aa5d0908`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d358d8a74bdba2fdc60d68954453d6af07570787f99fc70714b79be8aa5d0908`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d358d8a74bdba2fdc60d68954453d6af07570787f99fc70714b79be8aa5d0908`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/diagnostics_spec.spl
mirror: doc/06_spec/unit/app/lsp/diagnostics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/diagnostics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/diagnostics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/diagnostics_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates position with line and character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/diagnostics_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts at zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/diagnostics_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates range from positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
