# Trait Group From Execution Specification

> Tests covering generated trait-group .from() actually compiles and runs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Group From Execution Specification

## Scenarios

### generated trait-group .from() actually compiles and runs

#### the generated code is EXECUTED, not just text-matched

#### compiles -- no unresolved accessor on the desugared session struct

- compiles -- no unresolved accessor on the desugared session struct
   - Expected: o does not contain `method `debug` not found`
   - Expected: o does not contain `error: semantic`
   - Expected: o does not contain `error: compile failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles -- no unresolved accessor on the desugared session struct")
val o = run_generated()
expect(o.contains("method `debug` not found")).to_equal(false)
expect(o.contains("error: semantic")).to_equal(false)
expect(o.contains("error: compile failed")).to_equal(false)
```

</details>

#### acquires the group and reaches the driver's print

- acquires the group and reaches the driver's print
   - Expected: o contains `OBSERVED=`
   - Expected: o does not contain `ACQUIRED=NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquires the group and reaches the driver's print")
val o = run_generated()
expect(o.contains("OBSERVED=")).to_equal(true)
expect(o.contains("ACQUIRED=NONE")).to_equal(false)
```

</details>

#### REGRESSION -- one member's mutation is seen by the other member

#### a resume() driven through the group is counted by profile_end()

- a resume() driven through the group is counted by profile_end()
   - Expected: o contains `OBSERVED=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a resume() driven through the group is counted by profile_end()")
# THE bug. Paired-copy acquisition prints OBSERVED=0 here and
# passes every Some/None check ever written against it.
val o = run_generated()
expect(o.contains("OBSERVED=1")).to_equal(true)
```

</details>

#### does not report a zero measurement after a real mutation

- does not report a zero measurement after a real mutation
   - Expected: o does not contain `OBSERVED=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report a zero measurement after a real mutation")
val o = run_generated()
expect(o.contains("OBSERVED=0")).to_equal(false)
```

</details>

#### all-or-nothing acquisition still holds at RUNTIME

#### yields None when a member capability is absent

- yields None when a member capability is absent
   - Expected: o contains `MISSING_MEMBER=NONE`
   - Expected: o does not contain `MISSING_MEMBER=SOME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields None when a member capability is absent")
val o = run_generated()
expect(o.contains("MISSING_MEMBER=NONE")).to_equal(true)
expect(o.contains("MISSING_MEMBER=SOME")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/desugar/trait_group_from_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generated trait-group .from() actually compiles and runs.
- generated trait-group .from() actually compiles and runs

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

- Canonical SPipe generation for source `96aa557916642a70584575c3360d21999ec74b99e964dcf4164f65b7529b693d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96aa557916642a70584575c3360d21999ec74b99e964dcf4164f65b7529b693d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96aa557916642a70584575c3360d21999ec74b99e964dcf4164f65b7529b693d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/desugar/trait_group_from_execution_spec.spl
mirror: doc/06_spec/01_unit/app/desugar/trait_group_from_execution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/desugar/trait_group_from_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/desugar/trait_group_from_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/desugar/trait_group_from_execution_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles -- no unresolved accessor on the desugared session struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/desugar/trait_group_from_execution_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acquires the group and reaches the driver's print' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/desugar/trait_group_from_execution_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a resume() driven through the group is counted by profile_end()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
