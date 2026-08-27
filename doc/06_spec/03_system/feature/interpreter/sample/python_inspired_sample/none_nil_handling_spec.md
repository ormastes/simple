# None/Nil Handling (Interpreter)

> Tests nil/none value handling in the interpreter including optional chaining, nil coalescing, and nil checks. Verifies that nil values propagate correctly and that nil-safety features work as expected in interpreted mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# None/Nil Handling (Interpreter)

Tests nil/none value handling in the interpreter including optional chaining, nil coalescing, and nil checks. Verifies that nil values propagate correctly and that nil-safety features work as expected in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests nil/none value handling in the interpreter including optional chaining,
nil coalescing, and nil checks. Verifies that nil values propagate correctly
and that nil-safety features work as expected in interpreted mode.

## Scenarios

### None and Nil Handling

#### Option type basics

#### represents present value with Some

- represents present value with Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("represents present value with Some")
val opt: Option<i64> = Some(42)
expect opt.is_some() == true
```

</details>

#### represents absent value with None

- represents absent value with None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("represents absent value with None")
val opt: Option<i64> = nil
expect opt.is_none() == true
```

</details>

#### unwrapping values

#### unwraps Some value

- unwraps Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unwraps Some value")
val opt = Some(100)
expect opt.unwrap() == 100
```

</details>

#### provides default for None

- provides default for None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides default for None")
val opt: Option<i64> = nil
expect opt.unwrap_or(0) == 0
```

</details>

#### null coalescing

#### returns value when present

- returns value when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns value when present")
val opt = Some("hello")
val result = opt ?? "default"
expect result == "hello"
```

</details>

#### returns default when None

- returns default when None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns default when None")
val opt: Option<text> = nil
val result = opt ?? "default"
expect result == "default"
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63e7ef322d0e22246888779eadfb26ce115d40a3f81a8e24377128a59d4d3c85`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63e7ef322d0e22246888779eadfb26ce115d40a3f81a8e24377128a59d4d3c85`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63e7ef322d0e22246888779eadfb26ce115d40a3f81a8e24377128a59d4d3c85`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'represents present value with Some' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'represents absent value with None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps Some value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
