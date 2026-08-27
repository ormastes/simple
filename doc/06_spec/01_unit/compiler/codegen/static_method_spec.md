# Static Method Specification

> Tests covering Static method calls, Static method chaining, Static vs instance disambiguation, Static methods calling other methods, Static method control flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Method Specification

## Scenarios

### Static method calls

#### calls a static method with no parameters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls a static method with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a static method with no parameters")
val p = SmPoint.origin()
expect p.x + p.y to_equal 0
```

</details>

#### calls a static method with parameters

- calls a static method with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a static method with parameters")
val r = SmRectangle.create(5, 3)
expect r.width * r.height to_equal 15
```

</details>

#### returns values from static methods

- returns values from static methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns values from static methods")
val sum = SmMath.add(5, 3)
val product = SmMath.multiply(4, 2)
expect sum to_equal 8
expect product to_equal 8
expect sum + product to_equal 16
```

</details>

### Static method chaining

#### chains a static constructor with instance methods

- chains a static constructor with instance methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains a static constructor with instance methods")
var b = SmBuilder.new()
expect b.get() to_equal 0
b.set(42)
expect b.get() to_equal 42
```

</details>

#### runs multiple static calls in sequence

- runs multiple static calls in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs multiple static calls in sequence")
val c1 = SmCounter.zero()
val c2 = SmCounter.from_n(10)
expect c1.count to_equal 0
expect c2.count to_equal 10
expect c1.count + c2.count to_equal 10
```

</details>

### Static vs instance disambiguation

#### distinguishes static constructors from instance methods

- distinguishes static constructors from instance methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes static constructors from instance methods")
var calc = SmCalculator.create(5)
val doubled = calc.double()
expect doubled to_equal 10
calc.add(3)
expect calc.value to_equal 8
expect doubled + calc.value to_equal 18
```

</details>

### Static methods calling other methods

#### lets a static method call another static method

- lets a static method call another static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets a static method call another static method")
expect SmMath.sum_of_squares(3, 4) to_equal 25
```

</details>

#### lets a static method call an instance method on a created object

- lets a static method call an instance method on a created object


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets a static method call an instance method on a created object")
expect SmPoint.manhattan_from_origin(3, 4) to_equal 7
```

</details>

### Static method control flow

#### handles multiple return points

- handles multiple return points


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple return points")
expect SmValidator.validate(-5) to_equal 0
expect SmValidator.validate(50) to_equal 50
expect SmValidator.validate(150) to_equal 100
```

</details>

#### handles many parameters

- handles many parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many parameters")
expect SmCalculator.sum8(1, 2, 3, 4, 5, 6, 7, 8) to_equal 36
```

</details>

#### handles a deep recursive static call stack

- handles a deep recursive static call stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a deep recursive static call stack")
expect SmFibonacci.fib(10) to_equal 55
```

</details>

<details>
<summary>Advanced: handles repeated static calls in a loop</summary>

#### handles repeated static calls in a loop

- handles repeated static calls in a loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles repeated static calls in a loop")
var result = 0
var i = 0
while i < 1000:
    result = SmCounter.increment(result)
    i = i + 1
expect result to_equal 1000
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/static_method_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Static method calls, Static method chaining, Static vs instance disambiguation, Static methods calling other methods, Static method control flow.
- Static method calls
- Static method chaining
- Static vs instance disambiguation
- Static methods calling other methods
- Static method control flow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `fdb4e5dd4345027f3facc17b5e1bfd42c38b4388491f781e6cdcd3cd05cfef4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdb4e5dd4345027f3facc17b5e1bfd42c38b4388491f781e6cdcd3cd05cfef4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdb4e5dd4345027f3facc17b5e1bfd42c38b4388491f781e6cdcd3cd05cfef4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/static_method_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/static_method_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/static_method_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/static_method_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/static_method_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a static method with no parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/static_method_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a static method with parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/static_method_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns values from static methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
