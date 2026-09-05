# Definition Specification

> Tests covering Definition Handler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Definition Specification

## Scenarios

### Definition Handler

#### finds function definitions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds function definitions")
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 10, 20)
handler.register_definition("my_function", location)
val result = handler.find_definition("my_function")
check(result != nil)
```

</details>

#### finds variable definitions

- finds variable definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds variable definitions")
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 5, 15)
handler.register_definition("my_var", location)
val result = handler.find_definition("my_var")
check(result != nil)
```

</details>

#### finds class definitions

- finds class definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds class definitions")
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 25, 35)
handler.register_definition("MyClass", location)
val result = handler.find_definition("MyClass")
check(result != nil)
```

</details>

#### handles undefined symbols

- handles undefined symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles undefined symbols")
val handler = MockDefinitionHandler.new()
val result = handler.find_definition("undefined_symbol")
check(result == nil)
```

</details>

#### finds imported definitions

- finds imported definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds imported definitions")
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("imported.spl", 100, 110)
handler.register_definition("imported_fn", location)
val result = handler.find_definition("imported_fn")
check(result != nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/definition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Definition Handler.
- Definition Handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `51e10d7a8111a0b98dd20465fc61272867dc9c77c2d650f34a09e16248d7643f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51e10d7a8111a0b98dd20465fc61272867dc9c77c2d650f34a09e16248d7643f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51e10d7a8111a0b98dd20465fc61272867dc9c77c2d650f34a09e16248d7643f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/definition_spec.spl
mirror: doc/06_spec/unit/app/lsp/definition_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/definition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/definition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/definition_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds function definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/definition_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds variable definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/definition_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds class definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
