# Reproducing spec: interpreted `class` field read and method call

> Regression guard for the `981c88435e0` defect recorded in doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md: every interpreted `class` (reference-type, `ClassDef.is_value_type == false`) instance lost both field access and method dispatch, failing with `undefined field 'x': cannot access field on value of type 'object'` and ``method `now` not found on type `object` ``. `struct` (value type) was unaffected, which is the positive control below.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reproducing spec: interpreted `class` field read and method call

Regression guard for the `981c88435e0` defect recorded in doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md: every interpreted `class` (reference-type, `ClassDef.is_value_type == false`) instance lost both field access and method dispatch, failing with `undefined field 'x': cannot access field on value of type 'object'` and ``method `now` not found on type `object` ``. `struct` (value type) was unaffected, which is the positive control below.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression guard for the `981c88435e0` defect recorded in
doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md: every
interpreted `class` (reference-type, `ClassDef.is_value_type == false`)
instance lost both field access and method dispatch, failing with
`undefined field 'x': cannot access field on value of type 'object'` and
``method `now` not found on type `object` ``. `struct` (value type) was
unaffected, which is the positive control below.

This is the minimal reproduction, one `class` with one field and one `me`
method, paired with the byte-identical `struct` that always passed.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** N/A

## Research

**Research:** N/A

## Examples

`C(x: 3).x` must read `3` and `C(x: 3).now()` must return `3`. The same two
assertions against a `struct` are the positive control that isolates the
value-type/reference-type split as the discriminator.

## Scenarios

### Interpreted class instances resolve fields and methods

#### reads a field directly off a class instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a field directly off a class instance
- Construct a class instance and read its declared field
   - Expected: c.x equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a field directly off a class instance")
step("Construct a class instance and read its declared field")
var c = MinimalClass(x: 3)
expect(c.x).to_equal(3)
```

</details>

#### dispatches a `me` method declared in the class body

- dispatches a `me` method declared in the class body
- Call the class-body method that returns the field
   - Expected: c.now() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches a `me` method declared in the class body")
step("Call the class-body method that returns the field")
var c = MinimalClass(x: 3)
expect(c.now()).to_equal(3)
```

</details>

### Positive control -- struct (value type) was never affected

#### reads a field directly off a struct instance

- reads a field directly off a struct instance
- The same field read against a struct must also work
   - Expected: s.x equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a field directly off a struct instance")
step("The same field read against a struct must also work")
var s = MinimalStruct(x: 3)
expect(s.x).to_equal(3)
```

</details>

#### dispatches a `me` method declared in the struct body

- dispatches a `me` method declared in the struct body
- The same method call against a struct must also work
   - Expected: s.now() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches a `me` method declared in the struct body")
step("The same method call against a struct must also work")
var s = MinimalStruct(x: 3)
expect(s.now()).to_equal(3)
```

</details>

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

- Canonical SPipe generation for source `18446955afbe5e74e75c539707a9921af0c7df21541f35758fe92a73fe77d822`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18446955afbe5e74e75c539707a9921af0c7df21541f35758fe92a73fe77d822`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18446955afbe5e74e75c539707a9921af0c7df21541f35758fe92a73fe77d822`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a field directly off a class instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches a `me` method declared in the class body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a field directly off a struct instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
