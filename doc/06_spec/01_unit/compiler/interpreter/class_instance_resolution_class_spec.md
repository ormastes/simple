# Defect-class spec: every shape of `class` field/method resolution

> The `981c88435e0` defect (doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md) was unconditional for reference-type aggregates: `Value::aggregate` routed every `class` to `Value::ClassInstance`, a variant neither primary resolution path (field access in `interpreter/expr/calls.rs`, method dispatch in `interpreter_method/mod.rs`) had an arm for. This spec covers the whole defect CLASS rather than the single reproduction: static constructor, mutating `me` method, trait-`impl`-block method, a class stored in a collection, and a cross-module class imported from the stdlib -- each of which fails independently if any resolution path loses its `Value::Object` arm again.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Defect-class spec: every shape of `class` field/method resolution

The `981c88435e0` defect (doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md) was unconditional for reference-type aggregates: `Value::aggregate` routed every `class` to `Value::ClassInstance`, a variant neither primary resolution path (field access in `interpreter/expr/calls.rs`, method dispatch in `interpreter_method/mod.rs`) had an arm for. This spec covers the whole defect CLASS rather than the single reproduction: static constructor, mutating `me` method, trait-`impl`-block method, a class stored in a collection, and a cross-module class imported from the stdlib -- each of which fails independently if any resolution path loses its `Value::Object` arm again.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `981c88435e0` defect (doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md)
was unconditional for reference-type aggregates: `Value::aggregate` routed
every `class` to `Value::ClassInstance`, a variant neither primary resolution
path (field access in `interpreter/expr/calls.rs`, method dispatch in
`interpreter_method/mod.rs`) had an arm for. This spec covers the whole defect
CLASS rather than the single reproduction: static constructor, mutating `me`
method, trait-`impl`-block method, a class stored in a collection, and a
cross-module class imported from the stdlib -- each of which fails
independently if any resolution path loses its `Value::Object` arm again.

Positive controls: a `struct` exercising the same shapes, plus primitive and
collection assertions that never depended on aggregate resolution at all, so a
wholesale harness failure is distinguishable from this specific regression.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** N/A

## Research

**Research:** N/A

## Examples

`Counter.new()` builds via a static constructor; `bump()` mutates through
`self`; `label()` comes from a trait `impl` block, not the class body; a
`Counter` read back out of an array must still resolve its field and method;
and `FixedStepClock` from `common.ui.ui_frame_clock` proves the cross-module
case.

## Scenarios

### Class field and method resolution -- defect class

#### resolves a field on an instance built by a static constructor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a field on an instance built by a static constructor
- Static constructors return the same aggregate shape as a literal call
   - Expected: c.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a field on an instance built by a static constructor")
step("Static constructors return the same aggregate shape as a literal call")
var c = Counter.new()
expect(c.count).to_equal(0)
```

</details>

#### dispatches a mutating `me` method that writes through self

- dispatches a mutating `me` method that writes through self
- Two bumps must be observable in the field afterwards
   - Expected: c.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches a mutating `me` method that writes through self")
step("Two bumps must be observable in the field afterwards")
var c = Counter.new()
c.bump()
c.bump()
expect(c.count).to_equal(2)
```

</details>

#### dispatches a method declared in a trait impl block, not the class body

- dispatches a method declared in a trait impl block, not the class body
- impl-block methods resolve through a different path than class-body methods
   - Expected: c.label() equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches a method declared in a trait impl block, not the class body")
step("impl-block methods resolve through a different path than class-body methods")
var c = Counter(count: 4)
expect(c.label()).to_equal(40)
```

</details>

#### resolves fields and methods on a class read back out of a collection

- resolves fields and methods on a class read back out of a collection
- Storing and retrieving must not degrade the receiver
   - Expected: items[0].count equals `7`
   - Expected: items[0].label() equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves fields and methods on a class read back out of a collection")
step("Storing and retrieving must not degrade the receiver")
var items = [Counter(count: 7)]
expect(items[0].count).to_equal(7)
expect(items[0].label()).to_equal(70)
```

</details>

#### resolves fields and methods on a class imported from another module

- resolves fields and methods on a class imported from another module
- Cross-module classes take the same construction path
   - Expected: clock.current_us equals `0`
   - Expected: clock.now_micros() equals `0`
   - Expected: clock.now_micros() equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves fields and methods on a class imported from another module")
step("Cross-module classes take the same construction path")
var clock = FixedStepClock.new(1000)
expect(clock.current_us).to_equal(0)
expect(clock.now_micros()).to_equal(0)
clock.advance(250)
expect(clock.now_micros()).to_equal(250)
```

</details>

### Positive controls

#### struct (value type) resolves its field and method

- struct (value type) resolves its field and method
- struct was never affected and must stay green
   - Expected: p.x equals `5`
   - Expected: p.doubled() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("struct (value type) resolves its field and method")
step("struct was never affected and must stay green")
var p = PlainPoint(x: 5)
expect(p.x).to_equal(5)
expect(p.doubled()).to_equal(10)
```

</details>

#### primitives and collections resolve without any aggregate involved

- primitives and collections resolve without any aggregate involved
- Distinguishes this regression from a wholesale harness failure
   - Expected: nums.len() equals `3`
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("primitives and collections resolve without any aggregate involved")
step("Distinguishes this regression from a wholesale harness failure")
val nums = [1, 2, 3]
expect(nums.len()).to_equal(3)
expect(1 + 1).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `ec07f2ff943798cf2f8dc5544e47ffbb3c4fca51973dc0e4d169c8a7200602db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec07f2ff943798cf2f8dc5544e47ffbb3c4fca51973dc0e4d169c8a7200602db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec07f2ff943798cf2f8dc5544e47ffbb3c4fca51973dc0e4d169c8a7200602db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/class_instance_resolution_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/class_instance_resolution_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/class_instance_resolution_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a field on an instance built by a static constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches a mutating `me` method that writes through self' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches a method declared in a trait impl block, not the class body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
