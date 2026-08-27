# Auto Comprehensive 11 Specification

> Tests covering Comprehensive Test Suite.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auto Comprehensive 11 Specification

## Scenarios

### Comprehensive Test Suite

#### arithmetic coverage 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- arithmetic coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arithmetic coverage 1")
check(1 + 1 == 2)
check(5 - 3 == 2)
check(4 * 3 == 12)
check(10 / 2 == 5)
```

</details>

#### arithmetic coverage 2

- arithmetic coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arithmetic coverage 2")
check(7 % 3 == 1)
check(2 ** 3 == 8)
check(-5 * 2 == -10)
```

</details>

#### comparison coverage 1

- comparison coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comparison coverage 1")
check(5 > 3)
check(2 < 10)
check(5 >= 5)
check(3 <= 3)
```

</details>

#### comparison coverage 2

- comparison coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comparison coverage 2")
check(10 != 5)
check(5 == 5)
check(not (3 > 5))
```

</details>

#### boolean logic 1

- boolean logic 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boolean logic 1")
check(true and true)
check(not (true and false))
check(true or false)
check(not (false and false))
```

</details>

#### boolean logic 2

- boolean logic 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boolean logic 2")
check(not false)
check(not not true)
```

</details>

#### string coverage 1

- string coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string coverage 1")
val s = "hello"
check(s.len() == 5)
check(s.contains("ell"))
check(s.starts_with("hel"))
check(s.ends_with("llo"))
```

</details>

#### string coverage 2

- string coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string coverage 2")
val s = "test"
check(s[0..2] == "te")
check(s + "ing" == "testing")
```

</details>

#### array coverage 1

- array coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array coverage 1")
var arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
check(arr[0] == 1)
check(arr[4] == 5)
check(arr[-1] == 5)
```

</details>

#### array coverage 2

- array coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array coverage 2")
var arr = [10, 20, 30]
check(arr[0..2].len() == 2)
val appended = arr.append(40)
check(appended.len() == 4)
```

</details>

#### dict coverage 1

- dict coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict coverage 1")
val d = {"a": 1, "b": 2}
check(d["a"] == 1)
check(d["b"] == 2)
check(dict_keys(d).len() == 2)
```

</details>

#### dict coverage 2

- dict coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict coverage 2")
val d = {"key": "value"}
check(d.get("key") != nil)
check(d.get("missing") == nil)
```

</details>

#### option coverage 1

- option coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option coverage 1")
val opt = Some(42)
check(opt.?)
check(opt? == 42)
```

</details>

#### option coverage 2

- option coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option coverage 2")
val opt = nil
check(not opt.?)
```

</details>

#### range coverage 1

- range coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range coverage 1")
var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>

#### range coverage 2

- range coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range coverage 2")
var sum = 0
for i in 1..6:
    sum = sum + i
check(sum == 15)
```

</details>

#### conditional coverage 1

- conditional coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional coverage 1")
val x = 10
val result = if x > 5: "big" else: "small"
check(result == "big")
```

</details>

#### conditional coverage 2

- conditional coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional coverage 2")
val x = 2
val result = if x > 5: "big" else: "small"
check(result == "small")
```

</details>

#### match coverage 1

- match coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match coverage 1")
val x = Some(100)
val result = match x:
    Some(v): v * 2
    nil: 0
check(result == 200)
```

</details>

#### match coverage 2

- match coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match coverage 2")
val x = nil
val result = match x:
    Some(v): v * 2
    nil: -1
check(result == -1)
```

</details>

<details>
<summary>Advanced: loop coverage 1</summary>

#### loop coverage 1

- loop coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop coverage 1")
var total = 0
for i in [10, 20, 30]:
    total = total + i
check(total == 60)
```

</details>


</details>

<details>
<summary>Advanced: loop coverage 2</summary>

#### loop coverage 2

- loop coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop coverage 2")
fn run_while() -> i64:
    var i = 0
    while i < 5:
        i = i + 1
    i
check(run_while() == 5)
```

</details>


</details>

#### nested coverage 1

- nested coverage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested coverage 1")
val a = true
val b = true
if a:
    if b:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### nested coverage 2

- nested coverage 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested coverage 2")
val x = 10
val y = 20
if x < y:
    if y > 15:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### complex expression 1

- complex expression 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex expression 1")
val result = (1 + 2) * (3 + 4)
check(result == 21)
```

</details>

#### complex expression 2

- complex expression 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex expression 2")
val a = 10
val b = 5
val result = a * 2 + b / 5
check(result == 21)
```

</details>

#### chained comparison

- chained comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained comparison")
val x = 5
check(0 < x and x < 10)
```

</details>

#### ternary-like

- ternary-like


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ternary-like")
val x = 7
val result = if x % 2 == 0: "even" else: "odd"
check(result == "odd")
```

</details>

#### list comprehension simulation

- list comprehension simulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list comprehension simulation")
var evens = []
for i in 0..10:
    if i % 2 == 0:
        evens = evens.append(i)
check(evens.len() == 5)
```

</details>

#### error path

- error path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path")
var error = nil
check(error == nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/auto_comprehensive_11_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Comprehensive Test Suite.
- Comprehensive Test Suite

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `82c7a4589f8746db489d715b2132179e93ad576098fea9f58d9e0bfad583b474`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82c7a4589f8746db489d715b2132179e93ad576098fea9f58d9e0bfad583b474`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82c7a4589f8746db489d715b2132179e93ad576098fea9f58d9e0bfad583b474`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/auto_comprehensive_11_spec.spl
mirror: doc/06_spec/01_unit/lib/common/auto_comprehensive_11_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/auto_comprehensive_11_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/auto_comprehensive_11_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/auto_comprehensive_11_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arithmetic coverage 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/auto_comprehensive_11_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arithmetic coverage 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/auto_comprehensive_11_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comparison coverage 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
