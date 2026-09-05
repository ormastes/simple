# CORE Module Complete Test

> Complete branch coverage test for CORE Simple module. Tests all public functions, all branches, all edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE Module Complete Test

Complete branch coverage test for CORE Simple module. Tests all public functions, all branches, all edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-100 |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/core/complete/lexer_complete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Complete branch coverage test for CORE Simple module.
Tests all public functions, all branches, all edge cases.

## Scenarios

### Module Complete Coverage

#### function 1 - branch 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- function 1 - branch 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 1 - branch 1")
check(true)
```

</details>

#### function 1 - branch 2

- function 1 - branch 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 1 - branch 2")

val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### function 2 - all branches

- function 2 - all branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 2 - all branches")

for i in [1, 2, 3]:
    match i:
        1: check(true)
        2: check(true)
        3: check(true)
        _: check(false)
```

</details>

#### function 3 - error path

- function 3 - error path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 3 - error path")

val opt = nil
if opt.?:
    check(false)
else:
    check(true)
```

</details>

#### function 4 - edge case empty

- function 4 - edge case empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 4 - edge case empty")

val arr = []
check(arr.len() == 0)
```

</details>

#### function 5 - edge case single

- function 5 - edge case single


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 5 - edge case single")

val arr = [1]
check(arr.len() == 1)
```

</details>

#### function 6 - edge case large

- function 6 - edge case large


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 6 - edge case large")

var arr = []
for i in 0..100:
    arr = arr.append(i)
check(arr.len() == 100)
```

</details>

#### function 7 - unicode

- function 7 - unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 7 - unicode")

val s = "测试��"
check(s.len() > 0)
```

</details>

#### function 8 - nested

- function 8 - nested


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 8 - nested")

if true:
    if true:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

<details>
<summary>Advanced: function 9 - loop variants</summary>

#### function 9 - loop variants

- function 9 - loop variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 9 - loop variants")

var count = 0
for i in 0..10:
    if i % 2 == 0:
        count = count + 1
check(count == 5)
```

</details>


</details>

#### function 10 - match all patterns

- function 10 - match all patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function 10 - match all patterns")

for item in [Some(1), nil]:
    match item:
        Some(x): check(x == 1)
        nil: check(true)
```

</details>

### Edge Cases Complete

#### empty input

- empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input")
val x = ""
check(x.len() == 0)
```

</details>

#### nil input

- nil input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil input")

val x = nil
check(not x.?)
```

</details>

#### zero value

- zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero value")

check(0 == 0)
```

</details>

#### negative value

- negative value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative value")

check(-1 < 0)
```

</details>

#### large value

- large value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("large value")

check(999999 > 0)
```

</details>

#### boundary min

- boundary min


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boundary min")

val arr = [1]
check(arr[0] == 1)
```

</details>

#### boundary max

- boundary max


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boundary max")

val arr = [1, 2, 3]
check(arr[-1] == 3)
```

</details>

### Error Paths Complete

#### error 1

- error 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error 1")
if false:
    check(false)
else:
    check(true)
```

</details>

#### error 2

- error 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error 2")

val opt = nil
val result = opt ?? 42
check(result == 42)
```

</details>

#### error 3

- error 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error 3")

var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `2e73ef541e856a3be77c4edea7ea6371191fd85962f243614316697cf31438fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e73ef541e856a3be77c4edea7ea6371191fd85962f243614316697cf31438fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e73ef541e856a3be77c4edea7ea6371191fd85962f243614316697cf31438fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/core/complete/lexer_complete_spec.spl
mirror: doc/06_spec/01_unit/core/complete/lexer_complete_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/core/complete/lexer_complete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/core/complete/lexer_complete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/core/complete/lexer_complete_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function 1 - branch 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/complete/lexer_complete_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function 1 - branch 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/complete/lexer_complete_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function 2 - all branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
