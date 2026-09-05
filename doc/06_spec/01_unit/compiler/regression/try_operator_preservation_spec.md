# Try Operator Preservation Specification

> Tests covering Try operator `?` immediately after a call's closing `)`, Try operator `?` immediately after a nested `))` closing sequence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Try Operator Preservation Specification

## Scenarios

### Try operator `?` immediately after a call's closing `)`

#### propagates Err when the wrapped call fails

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- propagates Err when the wrapped call fails
   - Expected: msg equals `negative`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates Err when the wrapped call fails")
val result = tryop_outer_paren_then_try(-5)
match result:
    case Err(msg):
        expect(msg).to_equal("negative")
    case Ok(_):
        expect(false).to_equal(true)
```

</details>

#### unwraps Ok and continues past the `?` when the wrapped call succeeds

- unwraps Ok and continues past the `?` when the wrapped call succeeds
   - Expected: v equals `21`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps Ok and continues past the `?` when the wrapped call succeeds")
val result = tryop_outer_paren_then_try(10)
match result:
    case Ok(v):
        expect(v).to_equal(21)
    case Err(_):
        expect(false).to_equal(true)
```

</details>

### Try operator `?` immediately after a nested `))` closing sequence

#### still propagates Err through the extra parens

- still propagates Err through the extra parens
   - Expected: msg equals `negative`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still propagates Err through the extra parens")
val result = tryop_double_paren_then_try(-1)
match result:
    case Err(msg):
        expect(msg).to_equal("negative")
    case Ok(_):
        expect(false).to_equal(true)
```

</details>

#### still unwraps Ok through the extra parens

- still unwraps Ok through the extra parens
   - Expected: v equals `14`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still unwraps Ok through the extra parens")
val result = tryop_double_paren_then_try(7)
match result:
    case Ok(v):
        expect(v).to_equal(14)
    case Err(_):
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/regression/try_operator_preservation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Try operator `?` immediately after a call's closing `)`, Try operator `?` immediately after a nested `))` closing sequence.
- Try operator `?` immediately after a call's closing `)`
- Try operator `?` immediately after a nested `))` closing sequence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `845d8a4b42b2cb20c072dcfa470171c2515d8c2f1da75f0f1350070f544abda9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `845d8a4b42b2cb20c072dcfa470171c2515d8c2f1da75f0f1350070f544abda9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `845d8a4b42b2cb20c072dcfa470171c2515d8c2f1da75f0f1350070f544abda9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/regression/try_operator_preservation_spec.spl
mirror: doc/06_spec/01_unit/compiler/regression/try_operator_preservation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/regression/try_operator_preservation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/regression/try_operator_preservation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/regression/try_operator_preservation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/regression/try_operator_preservation_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates Err when the wrapped call fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/regression/try_operator_preservation_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps Ok and continues past the `?` when the wrapped call succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/regression/try_operator_preservation_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still propagates Err through the extra parens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
