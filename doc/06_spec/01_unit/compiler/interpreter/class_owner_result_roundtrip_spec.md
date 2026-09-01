# Class Owner Result Roundtrip Specification

> Tests covering class owner returned inside a struct survives the next call.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Owner Result Roundtrip Specification

## Scenarios

### class owner returned inside a struct survives the next call

#### preserves class mutation through two owner-result handoffs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves class mutation through two owner-result handoffs
- Mutate and return the class owner in a result struct
   - Expected: first.observed equals `1`
   - Expected: first.owner.value equals `1`
- Bind the returned owner and pass it through the same boundary
   - Expected: second.observed equals `2`
   - Expected: second.owner.value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves class mutation through two owner-result handoffs")
step("Mutate and return the class owner in a result struct")
var owner = OwnerResultCounter(value: 0)
val first = advance_owner(owner)
expect(first.observed).to_equal(1)
expect(first.owner.value).to_equal(1)

step("Bind the returned owner and pass it through the same boundary")
owner = first.owner
val second = advance_owner(owner)
expect(second.observed).to_equal(2)
expect(second.owner.value).to_equal(2)
```

</details>

#### keeps the wrapper value semantics independent of class identity

- keeps the wrapper value semantics independent of class identity
- A struct owner is copied, advanced, and returned explicitly
   - Expected: original.value equals `0`
   - Expected: advanced.observed equals `1`
   - Expected: advanced.owner.value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the wrapper value semantics independent of class identity")
step("A struct owner is copied, advanced, and returned explicitly")
val original = OwnerResultValueCounter(value: 0)
val advanced = advance_value(original)
expect(original.value).to_equal(0)
expect(advanced.observed).to_equal(1)
expect(advanced.owner.value).to_equal(1)
```

</details>

#### preserves mutation of a nested class state through both handoffs

- preserves mutation of a nested class state through both handoffs
- Use the service/state shape: a class owner contains class state
   - Expected: first.observed equals `1`
   - Expected: first.owner.state.value equals `1`
- Pass the returned owner into a second dispatch-like call
   - Expected: second.observed equals `2`
   - Expected: second.owner.state.value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves mutation of a nested class state through both handoffs")
step("Use the service/state shape: a class owner contains class state")
var owner = OwnerResultNestedOwner(
    state: OwnerResultNestedState(value: 0),
)
val first = advance_nested_owner(owner)
expect(first.observed).to_equal(1)
expect(first.owner.state.value).to_equal(1)

step("Pass the returned owner into a second dispatch-like call")
owner = first.owner
val second = advance_nested_owner(owner)
expect(second.observed).to_equal(2)
expect(second.owner.state.value).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering class owner returned inside a struct survives the next call.
- class owner returned inside a struct survives the next call

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

- Canonical SPipe generation for source `3ea4249a0fbe465d6f6cad3c108264fe1cfc4f497e4201fda06985f4d7c5f016`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ea4249a0fbe465d6f6cad3c108264fe1cfc4f497e4201fda06985f4d7c5f016`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ea4249a0fbe465d6f6cad3c108264fe1cfc4f497e4201fda06985f4d7c5f016`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves class mutation through two owner-result handoffs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the wrapper value semantics independent of class identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_owner_result_roundtrip_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves mutation of a nested class state through both handoffs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
