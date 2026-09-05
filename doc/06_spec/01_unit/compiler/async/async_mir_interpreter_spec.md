# Async Mir Interpreter Specification

> Tests covering Async MIR Instructions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Mir Interpreter Specification

## Scenarios

### Async MIR Instructions

#### CreatePromise

#### returns a value for the promise

- returns a value for the promise
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns a value for the promise")
# CreatePromise is synchronous in interpreter
expect(0).to_equal(0)
```

</details>

#### Await

#### passes through the promise value synchronously

- passes through the promise value synchronously
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes through the promise value synchronously")
# Await returns the input value in interpreter
expect(42).to_equal(42)
```

</details>

#### Yield

#### executes without error

- executes without error
   - Expected: "yield" equals `yield`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("executes without error")
expect("yield").to_equal("yield")
```

</details>

#### runtime function dispatch

#### handles create_promise

- handles create_promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles create_promise")
expect("create_promise").to_contain("promise")
```

</details>

#### handles await

- handles await
   - Expected: "await" equals `await`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles await")
expect("await").to_equal("await")
```

</details>

#### handles yield

- handles yield
   - Expected: "yield" equals `yield`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles yield")
expect("yield").to_equal("yield")
```

</details>

#### handles spawn

- handles spawn
   - Expected: "spawn" equals `spawn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles spawn")
expect("spawn").to_equal("spawn")
```

</details>

#### handles send

- handles send
   - Expected: "send" equals `send`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles send")
expect("send").to_equal("send")
```

</details>

#### handles receive

- handles receive
   - Expected: "receive" equals `receive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles receive")
expect("receive").to_equal("receive")
```

</details>

#### handles unknown function

- handles unknown function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles unknown function")
expect("unknown function").to_contain("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_mir_interpreter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Async MIR Instructions.
- Async MIR Instructions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `f4ec1eb60c32d585bf358b2640d67fa63e28642d2609c2a2937307a801b9b453`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4ec1eb60c32d585bf358b2640d67fa63e28642d2609c2a2937307a801b9b453`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4ec1eb60c32d585bf358b2640d67fa63e28642d2609c2a2937307a801b9b453`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/async/async_mir_interpreter_spec.spl
mirror: doc/06_spec/01_unit/compiler/async/async_mir_interpreter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/async/async_mir_interpreter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/async/async_mir_interpreter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/async/async_mir_interpreter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/async/async_mir_interpreter_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a value for the promise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_mir_interpreter_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through the promise value synchronously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_mir_interpreter_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
