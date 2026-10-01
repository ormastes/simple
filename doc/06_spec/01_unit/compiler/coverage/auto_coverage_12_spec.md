# Auto Coverage 12 Specification

> Tests covering Auto Coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auto Coverage 12 Specification

## Scenarios

### Auto Coverage

#### test 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- test 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 1")
check(1 == 1)
```

</details>

#### test 2

- test 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 2")
check("a" == "a")
```

</details>

#### test 3

- test 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 3")
val x = 5
check(x > 0)
```

</details>

#### test 4

- test 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 4")
val x = -1
check(x < 0)
```

</details>

#### test 5

- test 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 5")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### test 6

- test 6


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 6")
fn run_for() -> i64:
    var sum = 0
    for i in 0..10:
        sum = sum + 1
    sum
check(run_for() == 10)
```

</details>

#### test 7

- test 7


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 7")
val opt = Some(99)
match opt:
    Some(x): check(x == 99)
    nil: check(false)
```

</details>

#### test 8

- test 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 8")
val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### test 9

- test 9


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 9")
val s = "hello world"
check(s.len() == 11)
```

</details>

#### test 10

- test 10


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 10")
if true:
    check(true)
else:
    check(false)
```

</details>

#### test 11

- test 11


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 11")
if false:
    check(false)
else:
    check(true)
```

</details>

#### test 12

- test 12


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 12")
val a = 10
val b = 20
check(a < b)
```

</details>

#### test 13

- test 13


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 13")
val dict = {"key": "value"}
check(dict["key"] == "value")
```

</details>

#### test 14

- test 14


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 14")
fn run_while() -> i64:
    var count = 0
    while count < 5:
        count = count + 1
    count
check(run_while() == 5)
```

</details>

#### test 15

- test 15


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 15")
val x = 100
if x > 50:
    if x > 75:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### test 16

- test 16


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 16")
fn run_sum() -> i64:
    val nums = [10, 20, 30, 40, 50]
    var total = 0
    for n in nums:
        total = total + n
    total
check(run_sum() == 150)
```

</details>

#### test 17

- test 17


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 17")
val x = 42
val result = if x > 40: "big" else: "small"
check(result == "big")
```

</details>

#### test 18

- test 18


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 18")
val items = []
check(items.len() == 0)
```

</details>

#### test 19

- test 19


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 19")
val s1 = "hello"
val s2 = "world"
val combined = s1 + " " + s2
check(combined == "hello world")
```

</details>

#### test 20

- test 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("test 20")
val x = 10
val y = x * 2
check(y == 20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/coverage/auto_coverage_12_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Auto Coverage.
- Auto Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `6a1b9ef91e42c2db7abccd25d920db5839e7ac3e2d50526e653427fddc831dd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a1b9ef91e42c2db7abccd25d920db5839e7ac3e2d50526e653427fddc831dd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a1b9ef91e42c2db7abccd25d920db5839e7ac3e2d50526e653427fddc831dd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/coverage/auto_coverage_12_spec.spl
mirror: doc/06_spec/01_unit/compiler/coverage/auto_coverage_12_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/coverage/auto_coverage_12_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/coverage/auto_coverage_12_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 2' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 3' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 4' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 5' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/coverage/auto_coverage_12_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 6' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
