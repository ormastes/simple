# Union Type Specification

> Tests covering union types A | B.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Type Specification

## Scenarios

### union types A | B

#### function works with integer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- function works with integer
   - Expected: result equals `nonzero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function works with integer")
val result = accepts_value(42)
expect(result).to_equal("nonzero")
```

</details>

#### function works with zero

- function works with zero
   - Expected: result equals `zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function works with zero")
val result = accepts_value(0)
expect(result).to_equal("zero")
```

</details>

#### nullable with nil coalescing operator

- nullable with nil coalescing operator
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nullable with nil coalescing operator")
val x: i64 = 0
val result = x ?? 42
expect(result).to_equal(0)
```

</details>

#### nullable type with real value

- nullable type with real value
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nullable type with real value")
val result = nullable_int(99)
expect(result).to_equal(99)
```

</details>

#### match on typed value works

- match on typed value works
   - Expected: result equals `matched string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match on typed value works")
val x = "world"
val result = match x:
    case "world": "matched string"
    case _: "other"
expect(result).to_equal("matched string")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/union_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering union types A | B.
- union types A | B

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

- Canonical SPipe generation for source `dbfe448e12626af745c6f88be622f893ba97b4dbec033c5eca3c445ae5fe2edb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbfe448e12626af745c6f88be622f893ba97b4dbec033c5eca3c445ae5fe2edb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbfe448e12626af745c6f88be622f893ba97b4dbec033c5eca3c445ae5fe2edb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/parser/union_type_spec.spl
mirror: doc/06_spec/unit/compiler/parser/union_type_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/union_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/union_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/union_type_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/union_type_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function works with integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/union_type_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function works with zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/union_type_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nullable with nil coalescing operator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
