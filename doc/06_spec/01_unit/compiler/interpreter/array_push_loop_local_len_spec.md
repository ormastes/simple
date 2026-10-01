# Array Push Loop Local Len Specification

> Tests covering function-local array push loop + len (B1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Push Loop Local Len Specification

## Scenarios

### function-local array push loop + len (B1)

<details>
<summary>Advanced: len after 100 pushes in a local loop is 100</summary>

#### len after 100 pushes in a local loop is 100

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- len after 100 pushes in a local loop is 100
   - Expected: got equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("len after 100 pushes in a local loop is 100")
val got = push_loop_len(100)
expect(got).to_equal(100)
```

</details>


</details>

#### len after 3 pushes is 3

- len after 3 pushes is 3
   - Expected: got equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("len after 3 pushes is 3")
val got = push_loop_len(3)
expect(got).to_equal(3)
```

</details>

<details>
<summary>Advanced: last element after the loop is n-1 (contents intact)</summary>

#### last element after the loop is n-1 (contents intact)

- last element after the loop is n-1 (contents intact)
   - Expected: got equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("last element after the loop is n-1 (contents intact)")
val got = push_loop_last(100)
expect(got).to_equal(99)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering function-local array push loop + len (B1).
- function-local array push loop + len (B1)

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

- Canonical SPipe generation for source `7400d679d3365af73ccb5217c8b35a6581f9369a0fa674b25b62c5b0a2d97aa1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7400d679d3365af73ccb5217c8b35a6581f9369a0fa674b25b62c5b0a2d97aa1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7400d679d3365af73ccb5217c8b35a6581f9369a0fa674b25b62c5b0a2d97aa1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/array_push_loop_local_len_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/array_push_loop_local_len_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/array_push_loop_local_len_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'len after 100 pushes in a local loop is 100' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'len after 3 pushes is 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'last element after the loop is n-1 (contents intact)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
