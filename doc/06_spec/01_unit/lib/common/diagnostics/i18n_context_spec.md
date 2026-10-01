# I18n Context Specification

> Tests covering I18N Context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I18n Context Specification

## Scenarios

### I18N Context

#### should define severity names colors and priorities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define severity names colors and priorities
   - Expected: src contains `enum Severity`
   - Expected: src contains `Severity.Error: "error"`
   - Expected: src contains `Severity.Warning: "warning"`
   - Expected: src contains `fn color() -> text`
   - Expected: src contains `fn priority() -> i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define severity names colors and priorities")
val src = read_source("src/compiler/00.common/diagnostics/severity.spl")
expect(src.contains("enum Severity")).to_equal(true)
expect(src.contains("Severity.Error: \"error\"")).to_equal(true)
expect(src.contains("Severity.Warning: \"warning\"")).to_equal(true)
expect(src.contains("fn color() -> text")).to_equal(true)
expect(src.contains("fn priority() -> i32")).to_equal(true)
```

</details>

#### should expose severity predicates used by diagnostics

- should expose severity predicates used by diagnostics
   - Expected: src contains `fn is_error() -> bool`
   - Expected: src contains `Severity.Error: true`
   - Expected: src contains `fn is_warning() -> bool`
   - Expected: src contains `Severity.Warning: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose severity predicates used by diagnostics")
val src = read_source("src/compiler/00.common/diagnostics/severity.spl")
expect(src.contains("fn is_error() -> bool")).to_equal(true)
expect(src.contains("Severity.Error: true")).to_equal(true)
expect(src.contains("fn is_warning() -> bool")).to_equal(true)
expect(src.contains("Severity.Warning: true")).to_equal(true)
```

</details>

#### should define source spans with constructors and range formatting

- should define source spans with constructors and range formatting
   - Expected: src contains `struct Span`
   - Expected: src contains `static fn new(start: i64, end: i64, line: i64, col: i64) -> Span`
   - Expected: src contains `static fn default() -> Span`
   - Expected: src contains `fn to_range_string() -> text`
   - Expected: src contains `val end_col = self.col + (self.end - self.start)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define source spans with constructors and range formatting")
val src = read_source("src/compiler/00.common/diagnostics/span.spl")
expect(src.contains("struct Span")).to_equal(true)
expect(src.contains("static fn new(start: i64, end: i64, line: i64, col: i64) -> Span")).to_equal(true)
expect(src.contains("static fn default() -> Span")).to_equal(true)
expect(src.contains("fn to_range_string() -> text")).to_equal(true)
expect(src.contains("val end_col = self.col + (self.end - self.start)")).to_equal(true)
```

</details>

#### should define labels that bind messages to spans

- should define labels that bind messages to spans
   - Expected: src contains `struct Label`
   - Expected: src contains `static fn new(span: Span, message: text) -> Label`
   - Expected: src contains `static fn at(line: i64, column: i64, message: text) -> Label`
   - Expected: src contains `fn to_string() -> text`
   - Expected: src contains `self.span.to_string()`
   - Expected: src contains `self.message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define labels that bind messages to spans")
val src = read_source("src/compiler/00.common/diagnostics/label.spl")
expect(src.contains("struct Label")).to_equal(true)
expect(src.contains("static fn new(span: Span, message: text) -> Label")).to_equal(true)
expect(src.contains("static fn at(line: i64, column: i64, message: text) -> Label")).to_equal(true)
expect(src.contains("fn to_string() -> text")).to_equal(true)
expect(src.contains("self.span.to_string()")).to_equal(true)
expect(src.contains("self.message")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/i18n_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering I18N Context.
- I18N Context

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

- Canonical SPipe generation for source `2a3c3357fa0166febcf87ea12338b9916b135ad4e3cf5a3053dce0071a6b6569`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a3c3357fa0166febcf87ea12338b9916b135ad4e3cf5a3053dce0071a6b6569`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a3c3357fa0166febcf87ea12338b9916b135ad4e3cf5a3053dce0071a6b6569`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/diagnostics/i18n_context_spec.spl
mirror: doc/06_spec/01_unit/lib/common/diagnostics/i18n_context_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/diagnostics/i18n_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/diagnostics/i18n_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define severity names colors and priorities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define severity names colors and priorities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose severity predicates used by diagnostics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose severity predicates used by diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define source spans with constructors and range formatting' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define source spans with constructors and range formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/diagnostics/i18n_context_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define labels that bind messages to spans' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
