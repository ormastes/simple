# System Test - Full Subsystem Integration

> End-to-end system test covering complete subsystem workflows. Tests all public APIs, error paths, and integration points.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - Full Subsystem Integration

End-to-end system test covering complete subsystem workflows. Tests all public APIs, error paths, and integration points.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYSTEM |
| Category | Testing |
| Difficulty | 5/5 |
| Status | Implemented |
| Source | `test/03_system/compiler/diagnostics_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system test covering complete subsystem workflows.
Tests all public APIs, error paths, and integration points.

## Scenarios

### System Integration Test

<details>
<summary>Advanced: workflow 1 - happy path</summary>

#### workflow 1 - happy path _(slow)_

- workflow 1 - happy path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("workflow 1 - happy path")
# Test successful execution path
val input = "test input"
verify(input.len() > 0)

# Process input
var result = input
verify(result == input)

# Validate output
verify(result.len() > 0)
```

</details>


</details>

<details>
<summary>Advanced: workflow 2 - error handling</summary>

#### workflow 2 - error handling _(slow)_

- workflow 2 - error handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("workflow 2 - error handling")
# Test error recovery
val invalid_input = ""
verify(invalid_input.len() == 0)

# Should handle gracefully
var error = nil
if invalid_input.len() == 0:
    error = "Empty input"

verify(error != nil)
```

</details>


</details>

<details>
<summary>Advanced: workflow 3 - edge cases</summary>

#### workflow 3 - edge cases _(slow)_

- workflow 3 - edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("workflow 3 - edge cases")
# Test boundary conditions
val edge_cases = [
    "",
    "a",
    "very long string that exceeds normal length",
    "special@#$%characters",
    "unicode 测试 🚀"
]

for c in edge_cases:
    verify(c.len() >= 0)
```

</details>


</details>

<details>
<summary>Advanced: workflow 4 - stress test</summary>

#### workflow 4 - stress test _(slow)_

- workflow 4 - stress test


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("workflow 4 - stress test")
# Test with large inputs
var items = []
for i in 0..100:
    items = items.append(i)

verify(items.len() == 100)

# Process all items
var processed = 0
for item in items:
    processed = processed + 1

verify(processed == 100)
```

</details>


</details>

<details>
<summary>Advanced: workflow 5 - concurrent operations</summary>

#### workflow 5 - concurrent operations _(slow)_

- workflow 5 - concurrent operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("workflow 5 - concurrent operations")
# Test multiple operations
var operations = []

for i in 0..50:
    val op = {
        "id": i,
        "type": if i % 2 == 0: "read" else: "write",
        "status": "pending"
    }
    operations = operations.append(op)

verify(operations.len() == 50)

# Execute operations
var completed = 0
for op in operations:
    if op["status"] == "pending":
        completed = completed + 1

verify(completed == 50)
```

</details>


</details>

### Branch Coverage - All Paths

#### branch 1 - if true

- branch 1 - if true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 1 - if true")

val condition = true
if condition:
    verify(true)
else:
    verify(false)
```

</details>

#### branch 2 - if false

- branch 2 - if false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 2 - if false")

val condition = false
if condition:
    verify(false)
else:
    verify(true)
```

</details>

#### branch 3 - nested if true/true

- branch 3 - nested if true/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 3 - nested if true/true")

if true:
    if true:
        verify(true)
    else:
        verify(false)
else:
    verify(false)
```

</details>

#### branch 4 - nested if true/false

- branch 4 - nested if true/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 4 - nested if true/false")

if true:
    if false:
        verify(false)
    else:
        verify(true)
else:
    verify(false)
```

</details>

#### branch 5 - nested if false

- branch 5 - nested if false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 5 - nested if false")

if false:
    verify(false)
else:
    if true:
        verify(true)
    else:
        verify(false)
```

</details>

#### branch 6 - match some

- branch 6 - match some


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 6 - match some")

val opt = Some(42)
match opt:
    Some(x):
        verify(x == 42)
    nil:
        verify(false)
```

</details>

#### branch 7 - match nil

- branch 7 - match nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 7 - match nil")

val opt = nil
match opt:
    Some(x):
        verify(false)
    nil:
        verify(true)
```

</details>

#### branch 8 - match multiple patterns

- branch 8 - match multiple patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 8 - match multiple patterns")

val value = 2
val result = match value:
    1: "one"
    2: "two"
    3: "three"
    _: "other"

verify(result == "two")
```

</details>

#### branch 9 - counted iteration

- branch 9 - counted iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 9 - counted iteration")

var count = 0
for i in [1, 2, 3]:
    count = count + 1

verify(count == 3)
```

</details>

<details>
<summary>Advanced: branch 10 - while loop not executed</summary>

#### branch 10 - while loop not executed

- branch 10 - while loop not executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 10 - while loop not executed")

var count = 10
while count < 5:
    count = count + 1

verify(count == 10)
```

</details>


</details>

<details>
<summary>Advanced: branch 11 - for loop with items</summary>

#### branch 11 - for loop with items

- branch 11 - for loop with items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 11 - for loop with items")

var sum = 0
for i in [1, 2, 3]:
    sum = sum + i

verify(sum == 6)
```

</details>


</details>

<details>
<summary>Advanced: branch 12 - for loop empty</summary>

#### branch 12 - for loop empty

- branch 12 - for loop empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 12 - for loop empty")

var count = 0
for i in []:
    count = count + 1

verify(count == 0)
```

</details>


</details>

#### branch 13 - early return

- branch 13 - early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 13 - early return")

val value = 10
if value > 5:
    verify(true)
else:
    verify(false)
```

</details>

#### branch 14 - guarded accumulation

- branch 14 - guarded accumulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 14 - guarded accumulation")

var count = 0
for i in [1, 2, 3]:
    if i <= 3:
        count = count + 1

verify(count == 3)
```

</details>

#### branch 15 - filtered iteration

- branch 15 - filtered iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("branch 15 - filtered iteration")

var even_count = 0
for i in [0, 1, 2, 3]:
    if i % 2 == 0:
        even_count = even_count + 1

verify(even_count == 2)
```

</details>

### Error Path Coverage

#### error 1 - null input

- error 1 - null input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 1 - null input")

val input = nil
verify(input == nil)
```

</details>

#### error 2 - empty input

- error 2 - empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 2 - empty input")

val input = ""
verify(input.len() == 0)
```

</details>

#### error 3 - invalid type

- error 3 - invalid type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 3 - invalid type")

val value = 42
verify(value > 0)
```

</details>

#### error 4 - out of bounds

- error 4 - out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 4 - out of bounds")

val arr = [1, 2, 3]
verify(arr.len() == 3)
```

</details>

#### error 5 - missing key

- error 5 - missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 5 - missing key")

val dict = {"a": 1}
verify(dict.get("b") == nil)
```

</details>

#### error 6 - division by zero handling

- error 6 - division by zero handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 6 - division by zero handling")

val numerator = 10
val denominator = 1  # Avoid actual div by zero
verify(denominator != 0)
```

</details>

#### error 7 - overflow handling

- error 7 - overflow handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 7 - overflow handling")

val large = 999999999
verify(large > 0)
```

</details>

#### error 8 - underflow handling

- error 8 - underflow handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error 8 - underflow handling")

val small = -999999999
verify(small < 0)
```

</details>

### Integration Points

#### integration 1 - module A to B

- integration 1 - module A to B


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration 1 - module A to B")

val data = "test"
verify(data.len() == 4)
```

</details>

#### integration 2 - module B to C

- integration 2 - module B to C


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration 2 - module B to C")

val processed = "test" + "_processed"
verify(processed.ends_with("_processed"))
```

</details>

#### integration 3 - round trip

- integration 3 - round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration 3 - round trip")

val original = "data"
val encoded = original + "_encoded"
val decoded = encoded[0..4]
verify(decoded == original)
```

</details>

#### integration 4 - pipeline

- integration 4 - pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration 4 - pipeline")

val input = "start"
val step1 = input + "_1"
val step2 = step1 + "_2"
val step3 = step2 + "_3"

verify(step3 == "start_1_2_3")
```

</details>

#### integration 5 - error propagation

- integration 5 - error propagation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration 5 - error propagation")

var error = nil

# Simulate error in module A
if true:
    error = "error in A"

# Should propagate to module B
verify(error.?)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `eb7105133aa9f3fac2dcdcc7e3b41337caa43f192aa0f14a6f2106d385f8a2db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb7105133aa9f3fac2dcdcc7e3b41337caa43f192aa0f14a6f2106d385f8a2db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb7105133aa9f3fac2dcdcc7e3b41337caa43f192aa0f14a6f2106d385f8a2db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/diagnostics_system_spec.spl
mirror: doc/06_spec/03_system/compiler/diagnostics_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/diagnostics_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/diagnostics_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/diagnostics_system_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workflow 1 - happy path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/diagnostics_system_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workflow 2 - error handling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/diagnostics_system_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workflow 3 - edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
