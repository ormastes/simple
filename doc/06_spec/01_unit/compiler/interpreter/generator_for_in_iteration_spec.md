# Generator For In Iteration Specification

> Tests covering generator for-in iteration (S7).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generator For In Iteration Specification

## Scenarios

### generator for-in iteration (S7)

#### collects multi-yield generator values in order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects multi-yield generator values in order
   - Expected: got equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects multi-yield generator values in order")
val got = ordered_total()
expect(got).to_equal(123)
```

</details>

#### iterates a zero-yield generator zero times

- iterates a zero-yield generator zero times
   - Expected: got equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("iterates a zero-yield generator zero times")
val got = count_iterations()
expect(got).to_equal(0)
```

</details>

#### still iterates a plain function returning an array

- still iterates a plain function returning an array
   - Expected: got equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still iterates a plain function returning an array")
val got = plain_total()
expect(got).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generator for-in iteration (S7).
- generator for-in iteration (S7)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `aa8a7aa9ea64dda7c9a88d0b2c4ee1a2c0c06aaaa25580802a9f1d2fdde3208f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa8a7aa9ea64dda7c9a88d0b2c4ee1a2c0c06aaaa25580802a9f1d2fdde3208f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa8a7aa9ea64dda7c9a88d0b2c4ee1a2c0c06aaaa25580802a9f1d2fdde3208f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/generator_for_in_iteration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/generator_for_in_iteration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/generator_for_in_iteration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects multi-yield generator values in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iterates a zero-yield generator zero times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/generator_for_in_iteration_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still iterates a plain function returning an array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
