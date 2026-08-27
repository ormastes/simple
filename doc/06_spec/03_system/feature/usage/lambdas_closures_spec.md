# Lambdas and Closures Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lambdas and Closures Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2300 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/lambdas_closures_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lambda | Anonymous function defined inline with `\` syntax |
| Closure | Function that captures variables from enclosing scope |
| Higher-Order Function | Function taking or returning other functions |

## Scenarios

### Basic Lambdas

#### creates simple lambda

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates simple lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates simple lambda")
val double = \x: x * 2
expect double(21) == 42
```

</details>

#### creates lambda with multiple params

- creates lambda with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates lambda with multiple params")
val add = \x, y: x + y
expect add(15, 27) == 42
```

</details>

#### creates lambda with no params

- creates lambda with no params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates lambda with no params")
val answer = \: 42
expect answer() == 42
```

</details>

#### invokes lambda immediately

- invokes lambda immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("invokes lambda immediately")
val result = (\x: x + 5)(37)
expect result == 42
```

</details>

### Closures

#### captures outer variable

- captures outer variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures outer variable")
val multiplier = 10
val multiply = \x: x * multiplier
expect multiply(4) == 40
```

</details>

#### captures multiple variables

- captures multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures multiple variables")
val a = 10
val b = 5
val calc = \x: x * a + b
expect calc(3) == 35
```

</details>

#### nested lambda calls

- nested lambda calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested lambda calls")
val double = \x: x * 2
val add_one = \x: x + 1
expect add_one(double(20)) == 41
```

</details>

### Lambdas with Collections

#### maps with lambda

- maps with lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with lambda")
val numbers = [1, 2, 3]
val doubled = numbers.map(_ * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### filters with lambda

- filters with lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with lambda")
val numbers = [1, 2, 3, 4, 5, 6]
val evens = numbers.filter(_ % 2 == 0)
expect evens.len() == 3
```

</details>

#### reduces with lambda

- reduces with lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduces with lambda")
val numbers = [1, 2, 3, 4]
val sum = numbers.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

### Lambda Edge Cases

#### lambda returning lambda

- lambda returning lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda returning lambda")
fn make_adder(n):
    return \x: x + n
val add_five = make_adder(5)
expect add_five(10) == 15
```

</details>

#### lambda as function parameter

- lambda as function parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda as function parameter")
fn apply(f, x):
    return f(x)
expect apply(\x: x * 2, 21) == 42
```

</details>

#### lambda with conditional

- lambda with conditional


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda with conditional")
val abs = \x: if x < 0: -x else: x
expect abs(-5) == 5
expect abs(5) == 5
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

- Canonical SPipe generation for source `e3f827854c4ed7eb9bfdcac54851b870c5a1eb6a31a180e368bf0d570b46fd16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3f827854c4ed7eb9bfdcac54851b870c5a1eb6a31a180e368bf0d570b46fd16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3f827854c4ed7eb9bfdcac54851b870c5a1eb6a31a180e368bf0d570b46fd16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/lambdas_closures_spec.spl
mirror: doc/06_spec/03_system/feature/usage/lambdas_closures_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/lambdas_closures_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/lambdas_closures_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/lambdas_closures_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates simple lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/lambdas_closures_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates lambda with multiple params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/lambdas_closures_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates lambda with no params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
