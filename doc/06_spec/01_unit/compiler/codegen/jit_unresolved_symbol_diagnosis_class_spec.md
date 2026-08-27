# Jit Unresolved Symbol Diagnosis Class Specification

> Tests covering unresolved symbols are diagnosed identically on both execution lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Unresolved Symbol Diagnosis Class Specification

## Scenarios

### unresolved symbols are diagnosed identically on both execution lanes

#### runs valid code on both lanes (non-vacuity control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs valid code on both lanes (non-vacuity control)
- A well-formed program must succeed on both lanes, proving the harness drives real execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs valid code on both lanes (non-vacuity control)")
step("A well-formed program must succeed on both lanes, proving the harness drives real execution")
expect(run_case("interpreter", CONTROL)).to_contain("rc=0|")
expect(run_case("jit", CONTROL)).to_contain("rc=0|")
expect(run_case("jit", CONTROL)).to_contain("OK")
```

</details>

#### refuses a called list-type constructor instead of crashing

- refuses a called list-type constructor instead of crashing
- `[i64]()` calls a list literal as a function — the JIT SIGSEGV'd with rc=139 here
- rc=139 is signal death; the correct verdict is the interpreter's semantic diagnostic
   - Expected: jit does not contain `rc=139|`
- The interpreter is the reference verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses a called list-type constructor instead of crashing")
step("`[i64]()` calls a list literal as a function — the JIT SIGSEGV'd with rc=139 here")
val jit = run_case("jit", TYPED_CTOR)

step("rc=139 is signal death; the correct verdict is the interpreter's semantic diagnostic")
expect(jit.contains("rc=139|")).to_equal(false)
expect(jit).to_contain("rc=1|")
expect(jit).to_contain("variable `i64` not found")

step("The interpreter is the reference verdict")
expect(run_case("interpreter", TYPED_CTOR)).to_contain("variable `i64` not found")
```

</details>

#### refuses a read of an undefined variable instead of failing open

- refuses a read of an undefined variable instead of failing open
- This is the silent member of the class: the JIT executed the body and exited 0
- A fail-open is a wrong ANSWER, not a wrong error message — rc must not be 0 and the body must not have run
   - Expected: jit does not contain `rc=0|`
- An unresolved name must never be materialised as a value
   - Expected: jit does not contain `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses a read of an undefined variable instead of failing open")
step("This is the silent member of the class: the JIT executed the body and exited 0")
val jit = run_case("jit", UNDEF_VAR)

step("A fail-open is a wrong ANSWER, not a wrong error message — rc must not be 0 and the body must not have run")
expect(jit.contains("rc=0|")).to_equal(false)
expect(jit).to_contain("rc=1|")
expect(jit).to_contain("variable `undefined_var_xyz` not found")

step("An unresolved name must never be materialised as a value")
expect(jit.contains("OK")).to_equal(false)
```

</details>

#### generalises across every unresolved-name shape, matching the interpreter

- generalises across every unresolved-name shape, matching the interpreter
- Undefined function call — was already correct and must stay correct
- Undefined type construction
- No shape may produce a signal death on either lane
   - Expected: run_case("jit", UNDEF_FN) does not contain `rc=139|`
   - Expected: run_case("jit", UNDEF_TYPE) does not contain `rc=139|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalises across every unresolved-name shape, matching the interpreter")
step("Undefined function call — was already correct and must stay correct")
expect(run_case("jit", UNDEF_FN)).to_contain("rc=1|")
expect(run_case("interpreter", UNDEF_FN)).to_contain("rc=1|")

step("Undefined type construction")
expect(run_case("jit", UNDEF_TYPE)).to_contain("rc=1|")
expect(run_case("interpreter", UNDEF_TYPE)).to_contain("rc=1|")

step("No shape may produce a signal death on either lane")
expect(run_case("jit", UNDEF_FN).contains("rc=139|")).to_equal(false)
expect(run_case("jit", UNDEF_TYPE).contains("rc=139|")).to_equal(false)
```

</details>

#### never emits an unsafe stub for a body that failed to compile

- never emits an unsafe stub for a body that failed to compile
- The stub-fallback path would emit an empty function and silently misbehave — it must stay opt-in
- Compilation failure must end in a diagnostic, not in an executed empty stub
   - Expected: jit does not contain `rc=0|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never emits an unsafe stub for a body that failed to compile")
step("The stub-fallback path would emit an empty function and silently misbehave — it must stay opt-in")
val jit = run_case("jit", UNDEF_VAR)

step("Compilation failure must end in a diagnostic, not in an executed empty stub")
expect(jit).to_contain("not found")
expect(jit.contains("rc=0|")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unresolved symbols are diagnosed identically on both execution lanes.
- unresolved symbols are diagnosed identically on both execution lanes

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de9c5ef1f24494ae058d187dcca7e60829fe0d6dc0465152da6708af95f09351`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de9c5ef1f24494ae058d187dcca7e60829fe0d6dc0465152da6708af95f09351`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de9c5ef1f24494ae058d187dcca7e60829fe0d6dc0465152da6708af95f09351`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs valid code on both lanes (non-vacuity control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a called list-type constructor instead of crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/jit_unresolved_symbol_diagnosis_class_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a read of an undefined variable instead of failing open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
