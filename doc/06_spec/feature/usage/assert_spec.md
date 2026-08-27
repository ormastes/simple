# Assert Statement Specification

> expect(x > 0).to_equal(true)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assert Statement Specification

expect(x > 0).to_equal(true)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASSERT-001 to #ASSERT-012 |
| Category | Language \| Contracts |
| Status | Implemented |
| Source | `test/feature/usage/assert_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Basic assert
expect(x > 0).to_equal(true)

# Assert with message
expect(x > 0, "x must be positive").to_equal(true)

# Assert in function
use std.spec.step

fn validate(x: i64) -> i64:
expect(x >= 0, "input must be non-negative").to_equal(true)
x * 2
```

## Scenarios

### Basic Assert Statement

#### basic assert compiles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- basic assert compiles
   - Expected: x > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("basic assert compiles")
val x = 10
expect(x > 0).to_equal(true)
expect x == 10
```

</details>

#### assert with message compiles

- assert with message compiles
   - Expected: x > 0, "x must be positive" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert with message compiles")
val x = 10
expect(x > 0, "x must be positive").to_equal(true)
expect x == 10
```

</details>

#### multiple assert conditions

- multiple assert conditions
   - Expected: x < 100 is true
   - Expected: x >= 0, "x must be non-negative" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple assert conditions")
val x = 5
expect(x < 100).to_equal(true)
expect(x >= 0, "x must be non-negative").to_equal(true)
expect x == 5
```

</details>

### Assert in Functions

#### assert in function body

- assert in function body
   - Expected: x >= 0, "input must be non-negative" is true
   - Expected: x < 1000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert in function body")
fn validate_and_compute(x: i64) -> i64:
    expect(x >= 0, "input must be non-negative").to_equal(true)
    expect(x < 1000).to_equal(true)
    x * 2

expect validate_and_compute(50) == 100
```

</details>

#### multiple asserts in function

- multiple asserts in function
   - Expected: x > 0 is true
   - Expected: y > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple asserts in function")
fn validate(x: i64, y: i64) -> i64:
    expect(x > 0).to_equal(true)
    expect(y > 0).to_equal(true)
    expect(x).to_not_equal(y, "x and y must be different")
    x + y

expect validate(10, 20) == 30
```

</details>

### Assert with Expressions

#### assert with comparison

- assert with comparison
   - Expected: a < b is true
   - Expected: a + b equals `30`
   - Expected: a * 2 equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert with comparison")
val a = 10
val b = 20
expect(a < b).to_equal(true)
expect(a + b).to_equal(30)
expect(a * 2).to_equal(b)
expect true
```

</details>

#### assert with boolean logic

- assert with boolean logic
   - Expected: x > 0 and y > 0 is true
   - Expected: x < 100 or y < 100 is true
   - Expected: not (x < 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert with boolean logic")
val x = 10
val y = 20
expect(x > 0 and y > 0).to_equal(true)
expect(x < 100 or y < 100).to_equal(true)
expect(not (x < 0)).to_equal(true)
expect true
```

</details>

### Assert in Control Flow

#### assert in if block

- assert in if block
   - Expected: x < 1000, "must be under 1000 in positive branch" is true
   - Expected: x >= -100, "must be at least -100" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert in if block")
fn process(x: i64) -> i64:
    if x > 0:
        expect(x < 1000, "must be under 1000 in positive branch").to_equal(true)
        x * 2
    else:
        expect(x >= -100, "must be at least -100").to_equal(true)
        -x

expect process(50) == 100
```

</details>

<details>
<summary>Advanced: assert in loop</summary>

#### assert in loop

- assert in loop
   - Expected: i >= 0, "iteration counter must be non-negative" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert in loop")
fn sum_with_validation(n: i64) -> i64:
    var total = 0
    var i = 0
    while i < n:
        expect(i >= 0, "iteration counter must be non-negative").to_equal(true)
        total = total + i
        i = i + 1
    total

expect sum_with_validation(5) == 10
```

</details>


</details>

### Assert with Function Contracts

#### assert combined with contracts

- assert combined with contracts
   - Expected: x < 1000, "x must be reasonable" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assert combined with contracts")
fn compute(x: i64) -> i64:
    in:
        x >= 0
    out(ret):
        ret >= x
    # Runtime assertions for additional validation
    expect(x < 1000, "x must be reasonable").to_equal(true)
    x + 10

expect compute(50) == 60
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88720c2c8d0dbc9a22090b555269126727ad53f982e5d9b82e0d7db28fe475c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88720c2c8d0dbc9a22090b555269126727ad53f982e5d9b82e0d7db28fe475c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88720c2c8d0dbc9a22090b555269126727ad53f982e5d9b82e0d7db28fe475c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/assert_spec.spl
mirror: doc/06_spec/feature/usage/assert_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/assert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/assert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/assert_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/assert_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic assert compiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/assert_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assert with message compiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/assert_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple assert conditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
