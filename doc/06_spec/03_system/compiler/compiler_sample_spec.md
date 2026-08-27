# compiler_sample_spec

> Simple Compiler Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compiler_sample_spec

Simple Compiler Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_sample_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Compiler Tests
Feature: Simple language compilation
Category: Compiler System Tests
Status: Complete

Tests for Simple compiler basic operations including arithmetic, variables, control flow, and collections.

## Scenarios

### Simple Compiler

#### basic arithmetic

#### produces correct output for arithmetic

- produces correct output for arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces correct output for arithmetic")
val result = 2 + 3
expect(result).to(eq(5))
```

</details>

#### handles variables

- handles variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles variables")
val x = 10
val y = 20
val sum = x + y
expect(sum).to(eq(30))
```

</details>

#### control flow

#### handles basic control flow

- handles basic control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles basic control flow")
val x = 10
val result = "smaller"
if x > 5:
    result = "greater"
expect(result).to(eq("greater"))
```

</details>

#### collections

#### handles arrays

- handles arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles arrays")
val arr = [1, 2, 3]
expect(arr.len()).to(eq(3))
expect(arr[0]).to(eq(1))
```

</details>

#### handles dicts

- handles dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles dicts")
val d = {"name": "Alice", "age": 30}
expect(d["name"]).to(eq("Alice"))
expect(d["age"]).to(eq(30))
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1907982a63b0691718cddc4808be64183344c760163bff21189065a23e63025b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1907982a63b0691718cddc4808be64183344c760163bff21189065a23e63025b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1907982a63b0691718cddc4808be64183344c760163bff21189065a23e63025b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/compiler_sample_spec.spl
mirror: doc/06_spec/03_system/compiler/compiler_sample_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/compiler_sample_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/compiler_sample_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/compiler_sample_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct output for arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_sample_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_sample_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles basic control flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
