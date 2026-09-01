# Diagnostic Predicate Empty State Specification

> Tests covering compiler diagnostic predicates report false on empty state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostic Predicate Empty State Specification

## Scenarios

### compiler diagnostic predicates report false on empty state

#### CachedFunctionEffectInfo.has_violations is false for an empty violation list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CachedFunctionEffectInfo.has_violations is false for an empty violation list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CachedFunctionEffectInfo.has_violations is false for an empty violation list")
val info = CachedFunctionEffectInfo.empty("f")
expect info.violations.len() == 0
expect info.has_violations() == false
```

</details>

#### CachedFunctionEffectInfo.has_violations is true once a violation is recorded

- CachedFunctionEffectInfo.has_violations is true once a violation is recorded


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CachedFunctionEffectInfo.has_violations is true once a violation is recorded")
var info = CachedFunctionEffectInfo.empty("f")
info.violations = info.violations.push("io escapes pure fn")
expect info.has_violations() == true
```

</details>

#### VerificationChecker.has_violations is false for a fresh checker

- VerificationChecker.has_violations is false for a fresh checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VerificationChecker.has_violations is false for a fresh checker")
val checker = VerificationChecker.create(true)
expect checker.has_violations() == false
```

</details>

#### VerificationChecker.has_violations is true after add_violation

- VerificationChecker.has_violations is true after add_violation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VerificationChecker.has_violations is true after add_violation")
var checker = VerificationChecker.create(true)
checker.add_violation(VerificationRule.VTrusted, "f", "no contract")
expect checker.has_violations() == true
```

</details>

#### BindingSpecializer.has_bindings is false for an empty binding map

- BindingSpecializer.has_bindings is false for an empty binding map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BindingSpecializer.has_bindings is false for an empty binding map")
val spec = BindingSpecializer.create()
expect spec.has_bindings() == false
```

</details>

#### BindingSpecializer.has_bindings is true after add_binding

- BindingSpecializer.has_bindings is true after add_binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BindingSpecializer.has_bindings is true after add_binding")
var spec = BindingSpecializer.create()
spec.add_binding("Writer", "FileWriter")
expect spec.has_bindings() == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compiler diagnostic predicates report false on empty state.
- compiler diagnostic predicates report false on empty state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `cec69345b09da35b0f08b7c2d1b0fbfbe54501a35ba2aa531196b6a6c95b80ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cec69345b09da35b0f08b7c2d1b0fbfbe54501a35ba2aa531196b6a6c95b80ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cec69345b09da35b0f08b7c2d1b0fbfbe54501a35ba2aa531196b6a6c95b80ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl
mirror: doc/06_spec/01_unit/compiler/diagnostic_predicate_empty_state_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/diagnostic_predicate_empty_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/diagnostic_predicate_empty_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CachedFunctionEffectInfo.has_violations is false for an empty violation list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CachedFunctionEffectInfo.has_violations is true once a violation is recorded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VerificationChecker.has_violations is false for a fresh checker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
