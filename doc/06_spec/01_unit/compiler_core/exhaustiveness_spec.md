# Exhaustiveness Specification

> Tests covering Exhaustiveness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exhaustiveness Specification

## Scenarios

### Exhaustiveness

#### should expose semantic match exhaustiveness lint warnings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose semantic match exhaustiveness lint warnings
   - Expected: src contains `fn check_match_exhaustiveness(decl_indices: [i64]) -> [MatchExhaustivenessWar... (full value in folded executable source)`
   - Expected: src contains `var enum_variants: {text: [text]} = {}`
   - Expected: src contains `val fn_warnings = check_stmts_match(body, fn_name, enum_variants)`
   - Expected: src contains `fn analyze_match(scrutinee: i64, arm_indices: [i64], fn_name: text, enums: {t... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose semantic match exhaustiveness lint warnings")
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("fn check_match_exhaustiveness(decl_indices: [i64]) -> [MatchExhaustivenessWarning]")).to_equal(true)
expect(src.contains("var enum_variants: {text: [text]} = {}")).to_equal(true)
expect(src.contains("val fn_warnings = check_stmts_match(body, fn_name, enum_variants)")).to_equal(true)
expect(src.contains("fn analyze_match(scrutinee: i64, arm_indices: [i64], fn_name: text, enums: {text: [text]}) -> [MatchExhaustivenessWarning]")).to_equal(true)
```

</details>

#### should treat wildcard arms as exhaustive and flag unreachable arms

- should treat wildcard arms as exhaustive and flag unreachable arms
   - Expected: src contains `var has_wildcard = false`
   - Expected: src contains `if pat_name == "_"`
   - Expected: src contains `unreachable match arm after wildcard '_'`
   - Expected: src contains `if has_wildcard:`
   - Expected: src contains `return warnings`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should treat wildcard arms as exhaustive and flag unreachable arms")
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("var has_wildcard = false")).to_equal(true)
expect(src.contains("if pat_name == \"_\"")).to_equal(true)
expect(src.contains("unreachable match arm after wildcard '_'")).to_equal(true)
expect(src.contains("if has_wildcard:")).to_equal(true)
expect(src.contains("return warnings")).to_equal(true)
```

</details>

#### should report missing enum boolean option and result variants

- should report missing enum boolean option and result variants
   - Expected: src contains `val missing_text = missing.join(", ")`
   - Expected: src contains `MEXH001`
   - Expected: src contains `MEXH003`
   - Expected: src contains `MEXH005`
   - Expected: src contains `non-exhaustive match on`
   - Expected: src contains `add missing arms or a wildcard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should report missing enum boolean option and result variants")
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("val missing_text = missing.join(\", \")")).to_equal(true)
expect(src.contains("MEXH001")).to_equal(true)
expect(src.contains("MEXH003")).to_equal(true)
expect(src.contains("MEXH005")).to_equal(true)
expect(src.contains("non-exhaustive match on")).to_equal(true)
expect(src.contains("add missing arms or a wildcard")).to_equal(true)
```

</details>

#### should warn when unknown matches lack a default arm

- should warn when unknown matches lack a default arm
   - Expected: src contains `MEXH002`
   - Expected: src contains `match expression has no wildcard/default case`
   - Expected: src contains `add a '_' catch-all arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should warn when unknown matches lack a default arm")
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("MEXH002")).to_equal(true)
expect(src.contains("match expression has no wildcard/default case")).to_equal(true)
expect(src.contains("add a '_' catch-all arm")).to_equal(true)
```

</details>

#### should keep interpreter match warnings on no matched arm

- should keep interpreter match warnings on no matched arm
   - Expected: src contains `fn eval_match_expr(eid: i64) -> i64`
   - Expected: src contains `check_match_exhaustive(arm_ids, inferred_type)`
   - Expected: src contains `warning: non-exhaustive match - no arm matched value of type `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should keep interpreter match warnings on no matched arm")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(src.contains("fn eval_match_expr(eid: i64) -> i64")).to_equal(true)
expect(src.contains("check_match_exhaustive(arm_ids, inferred_type)")).to_equal(true)
expect(src.contains("warning: non-exhaustive match - no arm matched value of type ")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/exhaustiveness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Exhaustiveness.
- Exhaustiveness

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

- Canonical SPipe generation for source `7003bab184133f7d7a8bd1cbe5a1e66f1e55ca61bf8bb3f715a68712f20b6a2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7003bab184133f7d7a8bd1cbe5a1e66f1e55ca61bf8bb3f715a68712f20b6a2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7003bab184133f7d7a8bd1cbe5a1e66f1e55ca61bf8bb3f715a68712f20b6a2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/exhaustiveness_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/exhaustiveness_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/exhaustiveness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/exhaustiveness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/exhaustiveness_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose semantic match exhaustiveness lint warnings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/exhaustiveness_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose semantic match exhaustiveness lint warnings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/exhaustiveness_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat wildcard arms as exhaustive and flag unreachable arms' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/exhaustiveness_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should treat wildcard arms as exhaustive and flag unreachable arms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/exhaustiveness_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report missing enum boolean option and result variants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/exhaustiveness_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report missing enum boolean option and result variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/exhaustiveness_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should warn when unknown matches lack a default arm' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/exhaustiveness_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep interpreter match warnings on no matched arm' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
