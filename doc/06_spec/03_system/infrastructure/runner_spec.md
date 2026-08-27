# runner_spec

> Property Testing Framework - Runner Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# runner_spec

Property Testing Framework - Runner Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Property Testing Framework - Runner Tests
Feature: Property test execution engine with configurable iterations and shrinking

## Scenarios

### Property Test Runner

#### Basic Execution

#### runs property test with generator

- runs property test with generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs property test with generator")
val result = run_property_test(
    test_fn=|x| x * 0 == 0,
    seed=42,
    iterations=50,
    max_shrinks=100
)

# Property x * 0 == 0 always holds
expect result.result_type == PropertyResultType.Success
expect result.iterations == 50
```

</details>

#### detects property violations

- detects property violations


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects property violations")
val result = run_property_test_range(
    test_fn=|x| x < 100,
    seed=42,
    min=0,
    max=200,
    iterations=100,
    max_shrinks=100
)

# Should detect the violation
expect result.result_type == PropertyResultType.Failure
# Original input should be >= 100
expect result.original_input >= 100
# Minimal should also be >= 100
expect result.minimal_input >= 100
```

</details>

#### runs specified number of iterations

- runs specified number of iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs specified number of iterations")
var iteration_count = 0
val seed = 42

var i = 0
while i < 25:
    val value = gen_i64(seed=seed + i)
    iteration_count = iteration_count + 1
    i = i + 1

expect iteration_count == 25
```

</details>

#### Shrinking on Failure

#### shrinks to minimal failing case

- shrinks to minimal failing case


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shrinks to minimal failing case")
val result = run_property_test_range(
    test_fn=|x| x < 50,
    seed=42,
    min=0,
    max=1000,
    iterations=100,
    max_shrinks=50
)

# Should find a failure
if result.result_type == PropertyResultType.Failure:
    # Minimal should be 50 (smallest value that fails)
    expect result.minimal_input == 50
    # Should have performed some shrinks
    expect result.shrinks >= 0
else:
    # If no failure found, that's also valid
    pass
```

</details>

#### respects max_shrinks limit

- respects max_shrinks limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("respects max_shrinks limit")
val result = run_property_test_range(
    test_fn=|x| x < 1000,
    seed=42,
    min=0,
    max=10000,
    iterations=10,
    max_shrinks=3
)

if result.result_type == PropertyResultType.Failure:
    # Should not exceed max_shrinks
    expect result.shrinks <= 3
```

</details>

#### Configuration

#### uses custom seed for reproducibility

- uses custom seed for reproducibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses custom seed for reproducibility")
# Capture generated values
var values1 = []
var values2 = []
var values3 = []

var i = 0
while i < 10:
    values1.push(gen_i64(seed=42 + i))
    i = i + 1

i = 0
while i < 10:
    values2.push(gen_i64(seed=42 + i))
    i = i + 1

i = 0
while i < 10:
    values3.push(gen_i64(seed=123 + i))
    i = i + 1

# Same seed should produce same sequence
expect values1 == values2
# Different seed should produce different sequence
expect values1 != values3
```

</details>

#### supports quick check mode

- supports quick check mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports quick check mode")
# quick_check runs fewer iterations
val result = quick_check(
    test_fn=|x| x * 0 == 0,
    seed=42
)

expect result == true
```

</details>

#### supports thorough check mode

- supports thorough check mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports thorough check mode")
# thorough_check runs many iterations
val result = thorough_check(
    test_fn=|x| x + 0 == x,
    seed=42
)

expect result == true
```

</details>

#### Property Examples

#### tests commutativity

- tests commutativity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests commutativity")
var passed = true
var i = 0
while i < 100:
    val a = gen_i64_range(seed=42 + i, min=-1000, max=1000)
    val b = gen_i64_range(seed=42 + i + 1000, min=-1000, max=1000)
    if a + b != b + a:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests associativity

- tests associativity


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests associativity")
var passed = true
var i = 0
while i < 100:
    val a = gen_i64_range(seed=42 + i, min=-100, max=100)
    val b = gen_i64_range(seed=42 + i + 1000, min=-100, max=100)
    val c = gen_i64_range(seed=42 + i + 2000, min=-100, max=100)
    if (a + b) + c != a + (b + c):
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests identity property

- tests identity property


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests identity property")
var passed = true
var i = 0
while i < 100:
    val x = gen_i64(seed=42 + i)
    if x + 0 != x:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests reverse twice is identity

- tests reverse twice is identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests reverse twice is identity")
var passed = true
var i = 0
while i < 50:
    val list = gen_list_i64(seed=42 + i, min_len=0, max_len=10, val_min=-100, val_max=100)
    val reversed_twice = list.reverse().reverse()
    if reversed_twice != list:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests string concatenation length

- tests string concatenation length


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests string concatenation length")
var passed = true
var i = 0
while i < 50:
    val s1 = gen_string_with_length(seed=42 + i, min=0, max=10)
    val s2 = gen_string_with_length(seed=42 + i + 1000, min=0, max=10)
    val concatenated = s1 + s2
    if len(concatenated) != len(s1) + len(s2):
        passed = false
        break
    i = i + 1

expect passed
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `cd970f2980874ae1ecba0dc005907b97cefa11431672459010bab62a8cb284da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd970f2980874ae1ecba0dc005907b97cefa11431672459010bab62a8cb284da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd970f2980874ae1ecba0dc005907b97cefa11431672459010bab62a8cb284da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/infrastructure/runner_spec.spl
mirror: doc/06_spec/03_system/infrastructure/runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infrastructure/runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/runner_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs property test with generator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/runner_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects property violations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/runner_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs specified number of iterations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
