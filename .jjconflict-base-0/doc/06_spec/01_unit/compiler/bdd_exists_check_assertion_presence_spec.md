# Bdd Exists Check Assertion Presence Specification

> Tests covering exists-check in an assertion position.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Exists Check Assertion Presence Specification

## Scenarios

### exists-check in an assertion position

#### reports present for a var reassigned from nil to a string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports present for a var reassigned from nil to a string
   - Expected: error.? == true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports present for a var reassigned from nil to a string")
var error = nil
val invalid_input = ""
if invalid_input.len() == 0:
    error = "Empty input"
expect(error.? == true).to_equal(true)
```

</details>

#### reports absent for a dict miss

- reports absent for a dict miss
   - Expected: r.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports absent for a dict miss")
val d = {"a": 1}
val r = d.get("b")
expect(r.?).to_equal(false)
```

</details>

#### reports present for a dict hit

- reports present for a dict hit
   - Expected: hit.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports present for a dict hit")
val d2 = {"a": 1}
val hit = d2.get("a")
expect(hit.?).to_equal(true)
```

</details>

#### yields a strict bool, not the payload

- yields a strict bool, not the payload
   - Expected: got.? == true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields a strict bool, not the payload")
val d3 = {"k": 42}
val got = d3.get("k")
expect(got.? == true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_exists_check_assertion_presence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering exists-check in an assertion position.
- exists-check in an assertion position

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0b0fd4d093061089b7de70468f00ca179f55214335b97c68772d0234d2fb085`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0b0fd4d093061089b7de70468f00ca179f55214335b97c68772d0234d2fb085`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0b0fd4d093061089b7de70468f00ca179f55214335b97c68772d0234d2fb085`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bdd_exists_check_assertion_presence_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_exists_check_assertion_presence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_exists_check_assertion_presence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_exists_check_assertion_presence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_exists_check_assertion_presence_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports present for a var reassigned from nil to a string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_exists_check_assertion_presence_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports absent for a dict miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_exists_check_assertion_presence_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports present for a dict hit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
