# Option Exists Check Falsy Payload Specification

> Tests covering ExistsCheck in boolean context - falsy present payload.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Exists Check Falsy Payload Specification

## Scenarios

### ExistsCheck in boolean context - falsy present payload

#### if opt.? takes the then-branch for Some(0)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- if opt.? takes the then-branch for Some(0)
   - Expected: describe_option_dot_check(0) equals `some:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if opt.? takes the then-branch for Some(0)")
expect(describe_option_dot_check(0)).to_equal("some:0")
```

</details>

#### if opt.? takes the else-branch for nil

- if opt.? takes the else-branch for nil
   - Expected: describe_option_dot_check(nil) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if opt.? takes the else-branch for nil")
expect(describe_option_dot_check(nil)).to_equal("none")
```

</details>

#### if opt.? still works for a non-zero payload

- if opt.? still works for a non-zero payload
   - Expected: describe_option_dot_check(7) equals `some:7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if opt.? still works for a non-zero payload")
expect(describe_option_dot_check(7)).to_equal("some:7")
```

</details>

#### elif opt.? sees Some(0) as present

- elif opt.? sees Some(0) as present
   - Expected: describe_via_elif(nil, 0) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("elif opt.? sees Some(0) as present")
expect(describe_via_elif(nil, 0)).to_equal("b")
```

</details>

#### while opt.? sees Some(0) as present

- while opt.? sees Some(0) as present
   - Expected: count_while(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while opt.? sees Some(0) as present")
expect(count_while(0)).to_equal(1)
```

</details>

#### while opt.? sees nil as absent

- while opt.? sees nil as absent
   - Expected: count_while(nil) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while opt.? sees nil as absent")
expect(count_while(nil)).to_equal(0)
```

</details>

#### match arm guard opt.? sees Some(0) as present

- match arm guard opt.? sees Some(0) as present
   - Expected: guarded(0) equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("match arm guard opt.? sees Some(0) as present")
expect(guarded(0)).to_equal("present")
```

</details>

#### match arm guard opt.? sees nil as absent

- match arm guard opt.? sees nil as absent
   - Expected: guarded(nil) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("match arm guard opt.? sees nil as absent")
expect(guarded(nil)).to_equal("absent")
```

</details>

#### expression-form if opt.? sees Some(0) as present

- expression-form if opt.? sees Some(0) as present
   - Expected: expr_form(0) equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expression-form if opt.? sees Some(0) as present")
expect(expr_form(0)).to_equal("present")
```

</details>

#### expression-form if opt.? sees nil as absent

- expression-form if opt.? sees nil as absent
   - Expected: expr_form(nil) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expression-form if opt.? sees nil as absent")
expect(expr_form(nil)).to_equal("absent")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ExistsCheck in boolean context - falsy present payload.
- ExistsCheck in boolean context - falsy present payload

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f8c6e7226c30c5d4c04bcf725b745c69acdb93cf105775ed2b7900cb5df1516`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f8c6e7226c30c5d4c04bcf725b745c69acdb93cf105775ed2b7900cb5df1516`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f8c6e7226c30c5d4c04bcf725b745c69acdb93cf105775ed2b7900cb5df1516`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl
mirror: doc/06_spec/03_system/interpreter/option_exists_check_falsy_payload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/interpreter/option_exists_check_falsy_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/interpreter/option_exists_check_falsy_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if opt.? takes the then-branch for Some(0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if opt.? takes the else-branch for nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/option_exists_check_falsy_payload_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if opt.? still works for a non-zero payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
