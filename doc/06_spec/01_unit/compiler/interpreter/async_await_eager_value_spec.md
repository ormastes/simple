# Async Await Eager Value Specification

> Tests covering await on async fn (B2 eager-async).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Await Eager Value Specification

## Scenarios

### await on async fn (B2 eager-async)

#### zero-arg async fn

#### returns the body value, not NIL/3

- returns the body value, not NIL/3
   - Expected: got equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the body value, not NIL/3")
val got = run_await_42()
expect(got).to_equal(42)
```

</details>

#### async fn with args

#### returns the computed value

- returns the computed value
   - Expected: got equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the computed value")
val got = run_await_add()
expect(got).to_equal(42)
```

</details>

#### await inside expression position

#### awaited value usable in arithmetic

- awaited value usable in arithmetic
   - Expected: got equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("awaited value usable in arithmetic")
val got = run_await_42() + 8
expect(got).to_equal(50)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering await on async fn (B2 eager-async).
- await on async fn (B2 eager-async)

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

- Canonical SPipe generation for source `eab53afb63b46699ba5842578748d12f034216b6b9f55a33718e3ceb551d4de7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eab53afb63b46699ba5842578748d12f034216b6b9f55a33718e3ceb551d4de7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eab53afb63b46699ba5842578748d12f034216b6b9f55a33718e3ceb551d4de7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/async_await_eager_value_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/async_await_eager_value_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/async_await_eager_value_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the body value, not NIL/3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the computed value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'awaited value usable in arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
