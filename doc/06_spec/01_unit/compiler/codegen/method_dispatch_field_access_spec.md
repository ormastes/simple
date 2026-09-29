# Method Dispatch Field Access Specification

> Tests covering method dispatch — field-access / index / tuple receiver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Dispatch Field Access Specification

## Scenarios

### method dispatch — field-access / index / tuple receiver

#### field-access receiver (`container.widget.init()`)

#### dispatches through the struct field's declared type

- dispatches through the struct field's declared type
   - Expected: container.widget.last equals `701`
   - Expected: container.other.tag equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches through the struct field's declared type")
# `container.widget` has `receiver.ty == FieldInitA` only when
# the field-type recovery path walks into the struct's field
# table. If that path is missing, the call mis-dispatches to
# `FieldInitB.init` and `last` stays at 0 (or `tag` flips).
var container: FieldInitContainer = FieldInitContainer.new()
container.widget.init()
expect(container.widget.last).to_equal(701)
expect(container.other.tag).to_equal(0)
```

</details>

#### index-access receiver (`arr[i].init()`)

#### dispatches through the array element type

- dispatches through the array element type
   - Expected: arr[0].last equals `701`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches through the array element type")
var arr: [FieldInitA; 2] = [FieldInitA.new(), FieldInitA.new()]
arr[0].init()
expect(arr[0].last).to_equal(701)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering method dispatch — field-access / index / tuple receiver.
- method dispatch — field-access / index / tuple receiver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `7eef749302da4a1955c1c9cd1d302730d6b3596f13701aacd55a98c1c98b6633`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7eef749302da4a1955c1c9cd1d302730d6b3596f13701aacd55a98c1c98b6633`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7eef749302da4a1955c1c9cd1d302730d6b3596f13701aacd55a98c1c98b6633`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/method_dispatch_field_access_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/method_dispatch_field_access_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/method_dispatch_field_access_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the struct field's declared type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through the array element type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
