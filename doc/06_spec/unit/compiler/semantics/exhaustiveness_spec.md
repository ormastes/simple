# Exhaustiveness Specification

> Tests covering exhaustiveness checking.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exhaustiveness Specification

## Scenarios

### exhaustiveness checking

#### exhaustive match with wildcard succeeds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exhaustive match with wildcard succeeds
   - Expected: result equals `five`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exhaustive match with wildcard succeeds")
val x = 5
val result = match x:
    case 5: "five"
    case _: "other"
expect(result).to_equal("five")
```

</details>

#### match with all cases covered works

- match with all cases covered works
   - Expected: result equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with all cases covered works")
val y = true
val result = match y:
    case true: "yes"
    case false: "no"
expect(result).to_equal("yes")
```

</details>

#### or-pattern covers multiple cases

- or-pattern covers multiple cases
   - Expected: result equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern covers multiple cases")
val z = 2
val result = match z:
    case 1 | 2 | 3: "small"
    case _: "big"
expect(result).to_equal("small")
```

</details>

#### match with nil coverage works

- match with nil coverage works
   - Expected: result equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with nil coverage works")
val opt = nil
val result = match opt:
    case nil: "none"
    case _: "some"
expect(result).to_equal("none")
```

</details>

#### guard prevents false match fallthrough

- guard prevents false match fallthrough
   - Expected: result equals `correct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard prevents false match fallthrough")
val n = 10
val result = match n:
    case 10 if n > 100: "impossible"
    case _: "correct"
expect(result).to_equal("correct")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/exhaustiveness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering exhaustiveness checking.
- exhaustiveness checking

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

- Canonical SPipe generation for source `ebf5187962dc7151531596e21fc5f173676dac302635260b46d2366ebaf6f9b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebf5187962dc7151531596e21fc5f173676dac302635260b46d2366ebaf6f9b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebf5187962dc7151531596e21fc5f173676dac302635260b46d2366ebaf6f9b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/exhaustiveness_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/exhaustiveness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/exhaustiveness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/exhaustiveness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/exhaustiveness_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exhaustive match with wildcard succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/exhaustiveness_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'match with all cases covered works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/exhaustiveness_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'or-pattern covers multiple cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
