# Absent Declared Types Specification

> Tests covering any-escape pass tolerates absent declared types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Absent Declared Types Specification

## Scenarios

### any-escape pass tolerates absent declared types

#### checks an inferred let binding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- checks an inferred let binding
   - Expected: inferred_local equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks an inferred let binding")
val inferred_local = 5 + 6
expect(inferred_local).to_equal(11)
```

</details>

#### checks a function with an untyped parameter

- checks a function with an untyped parameter
   - Expected: takes_untyped_param(4) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks a function with an untyped parameter")
expect(takes_untyped_param(4)).to_equal(8)
```

</details>

#### checks a function with no declared return type

- checks a function with no declared return type
   - Expected: returns_without_annotation(6) equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks a function with no declared return type")
expect(returns_without_annotation(6)).to_equal(12)
```

</details>

#### checks a closure with an untyped parameter

- checks a closure with an untyped parameter
   - Expected: applies_closure(10) equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks a closure with an untyped parameter")
expect(applies_closure(10)).to_equal(13)
```

</details>

#### checks a class field with an inferred type

- checks a class field with an inferred type
   - Expected: holder.bump(5) equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks a class field with an inferred type")
val holder = HolderWithInferredField()
expect(holder.bump(5)).to_equal(12)
```

</details>

#### checks a module-level global with an inferred type

- checks a module-level global with an inferred type
   - Expected: inferred_global + 1 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks a module-level global with an inferred type")
expect(inferred_global + 1).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering any-escape pass tolerates absent declared types.
- any-escape pass tolerates absent declared types

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73111a1e25888228d10a28662785f26b57b8f8c66ef92e0dd1086f931f423c24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73111a1e25888228d10a28662785f26b57b8f8c66ef92e0dd1086f931f423c24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73111a1e25888228d10a28662785f26b57b8f8c66ef92e0dd1086f931f423c24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks an inferred let binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks a function with an untyped parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/absent_declared_types_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks a function with no declared return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
