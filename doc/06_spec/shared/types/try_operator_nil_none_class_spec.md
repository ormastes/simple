# Try Operator Nil None Class Specification

> Tests covering Try operator nil/None propagation class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Try Operator Nil None Class Specification

## Scenarios

### Try operator nil/None propagation class

#### nil sources propagate as None

#### propagates a directly returned nil

- propagates a directly returned nil
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates a directly returned nil")
val r = try_nil_direct()
val is_none = r.is_none()
expect(is_none).to_equal(true)
```

</details>

#### propagates nil that follows a successful Some

- propagates nil that follows a successful Some
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates nil that follows a successful Some")
val r = try_nil_after_some()
val is_none = r.is_none()
expect(is_none).to_equal(true)
```

</details>

#### propagates nil through a nested call stack

- propagates nil through a nested call stack
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates nil through a nested call stack")
val r = try_nil_middle_layer()
val is_none = r.is_none()
expect(is_none).to_equal(true)
```

</details>

#### positive controls (must stay passing)

#### still unwraps Some through ?

- still unwraps Some through ?
   - Expected: is_some is true
   - Expected: v equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("still unwraps Some through ?")
val r = try_some_only()
val is_some = r.is_some()
expect(is_some).to_equal(true)
val v = r.unwrap()
expect(v).to_equal(7)
```

</details>

#### still unwraps Ok through ?

- still unwraps Ok through ?
   - Expected: is_ok is true
   - Expected: v equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("still unwraps Ok through ?")
val r = try_result_ok()
val is_ok = r.is_ok()
expect(is_ok).to_equal(true)
val v = r.unwrap()
expect(v).to_equal(10)
```

</details>

#### still propagates Err through ?

- still propagates Err through ?
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("still propagates Err through ?")
val r = try_result_err()
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/try_operator_nil_none_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Try operator nil/None propagation class.
- Try operator nil/None propagation class

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

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75b63cd88ca89c146158705b9de136b6a632b165037de56d7ac7e5c9c73fc7f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75b63cd88ca89c146158705b9de136b6a632b165037de56d7ac7e5c9c73fc7f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75b63cd88ca89c146158705b9de136b6a632b165037de56d7ac7e5c9c73fc7f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/shared/types/try_operator_nil_none_class_spec.spl
mirror: doc/06_spec/shared/types/try_operator_nil_none_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/types/try_operator_nil_none_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/types/try_operator_nil_none_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/types/try_operator_nil_none_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/shared/types/try_operator_nil_none_class_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates a directly returned nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/try_operator_nil_none_class_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates nil that follows a successful Some' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/try_operator_nil_none_class_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates nil through a nested call stack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
