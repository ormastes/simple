# Must Use Specification

> Tests covering Must Use.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Must Use Specification

## Scenarios

### Must Use

#### should expose must_use registry functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose must_use registry functions
   - Expected: src contains `fn must_use_register(name: text, reason: text)`
   - Expected: src contains `fn must_use_is_registered(name: text) -> bool`
   - Expected: src contains `fn must_use_get_reason(name: text) -> text`
   - Expected: src contains `fn must_use_scan_source(source: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose must_use registry functions")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(src.contains("fn must_use_register(name: text, reason: text)")).to_equal(true)
expect(src.contains("fn must_use_is_registered(name: text) -> bool")).to_equal(true)
expect(src.contains("fn must_use_get_reason(name: text) -> text")).to_equal(true)
expect(src.contains("fn must_use_scan_source(source: text)")).to_equal(true)
```

</details>

#### should scan must_use annotations and optional reasons

- should scan must_use annotations and optional reasons
   - Expected: src contains `if trimmed.starts_with("# @must_use")`
   - Expected: src contains `pending_must_use = true`
   - Expected: src contains `"if trimmed`
   - Expected: src contains `pending_reason = reason_chars.join("")`
   - Expected: src contains `must_use_register(fname, pending_reason)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should scan must_use annotations and optional reasons")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(src.contains("if trimmed.starts_with(\"# @must_use\")")).to_equal(true)
expect(src.contains("pending_must_use = true")).to_equal(true)
expect(src.contains("if trimmed.contains(\"(\\\"\")")).to_equal(true)
expect(src.contains("pending_reason = reason_chars.join(\"\")")).to_equal(true)
expect(src.contains("must_use_register(fname, pending_reason)")).to_equal(true)
```

</details>

#### should enable critical profile mode from source annotations

- should enable critical profile mode from source annotations
   - Expected: tables_src contains `if trimmed.starts_with("# @profile(critical)")`
   - Expected: tables_src contains `must_use_critical_mode = true`
   - Expected: mod_src contains `must_use_scan_source(source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should enable critical profile mode from source annotations")
val tables_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
val mod_src = read_source("src/compiler/10.frontend/core/interpreter/mod.spl")
expect(tables_src.contains("if trimmed.starts_with(\"# @profile(critical)\")")).to_equal(true)
expect(tables_src.contains("must_use_critical_mode = true")).to_equal(true)
expect(mod_src.contains("must_use_scan_source(source)")).to_equal(true)
```

</details>

#### should emit R9 errors and help for ignored must_use calls

- should emit R9 errors and help for ignored must_use calls
   - Expected: src contains `if must_use_is_registered(fn_name)`
   - Expected: src contains `error[R9]: return value of function '`
   - Expected: src contains `must be used`
   - Expected: src contains `= help: assign to variable or use 'val _ = ...' to discard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should emit R9 errors and help for ignored must_use calls")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("if must_use_is_registered(fn_name)")).to_equal(true)
expect(src.contains("error[R9]: return value of function '")).to_equal(true)
expect(src.contains("must be used")).to_equal(true)
expect(src.contains("= help: assign to variable or use 'val _ = ...' to discard")).to_equal(true)
```

</details>

#### should emit R9 errors in critical profile mode

- should emit R9 errors in critical profile mode
   - Expected: src contains `elif must_use_critical_mode`
   - Expected: src contains `discarded in @profile(critical)`
   - Expected: src contains `warning: return value of type '`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should emit R9 errors in critical profile mode")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("elif must_use_critical_mode")).to_equal(true)
expect(src.contains("discarded in @profile(critical)")).to_equal(true)
expect(src.contains("warning: return value of type '")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/must_use_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Must Use.
- Must Use

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1268918e8461c6cd2aa94223708e1b38f778b7fc491e0290fb9e5c9d9a26e5a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1268918e8461c6cd2aa94223708e1b38f778b7fc491e0290fb9e5c9d9a26e5a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1268918e8461c6cd2aa94223708e1b38f778b7fc491e0290fb9e5c9d9a26e5a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/must_use_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/must_use_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/must_use_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/must_use_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/must_use_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose must_use registry functions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/must_use_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose must_use registry functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/must_use_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should scan must_use annotations and optional reasons' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/must_use_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should scan must_use annotations and optional reasons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/must_use_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enable critical profile mode from source annotations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/must_use_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enable critical profile mode from source annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/must_use_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit R9 errors and help for ignored must_use calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/must_use_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit R9 errors in critical profile mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
