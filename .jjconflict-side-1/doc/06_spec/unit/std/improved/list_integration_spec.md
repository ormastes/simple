# STDLIB Module Comprehensive Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Module Comprehensive Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STDLIB |
| Category | Standard Library |
| Status | Implemented |
| Source | `test/unit/std/improved/list_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### STDLIB Module Complete Test

#### basic operation 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- basic operation 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic operation 1")
check(1 + 1 == 2)
```

</details>

#### basic operation 2

- basic operation 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic operation 2")

val x = "test"
check(x.len() == 4)
```

</details>

#### basic operation 3

- basic operation 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic operation 3")

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### type conversion 1

- type conversion 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type conversion 1")

val s = "42"
check(s.len() == 2)
```

</details>

#### type conversion 2

- type conversion 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type conversion 2")

val num = 42
check(num > 0)
```

</details>

#### collection operations 1

- collection operations 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collection operations 1")

val arr = [1, 2, 3, 4, 5]
var sum = 0
for x in arr:
    sum = sum + x
check(sum == 15)
```

</details>

#### collection operations 2

- collection operations 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collection operations 2")

var arr = [1, 2, 3]
val result = arr.append(4)
check(result.len() == 4)
```

</details>

#### collection operations 3

- collection operations 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collection operations 3")

val arr = [1, 2, 3, 4, 5]
var evens = []
for x in arr:
    if x % 2 == 0:
        evens = evens.append(x)
check(evens.len() == 2)
```

</details>

#### string operations 1

- string operations 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string operations 1")

val s = "hello"
check(s.starts_with("hel"))
```

</details>

#### string operations 2

- string operations 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string operations 2")

val s = "world"
check(s.ends_with("rld"))
```

</details>

#### string operations 3

- string operations 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string operations 3")

val s = "test string"
check(s.contains("str"))
```

</details>

#### option handling 1

- option handling 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option handling 1")

val opt = Some(42)
check(opt.?)
check(opt? == 42)
```

</details>

#### option handling 2

- option handling 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option handling 2")

val opt = nil
check(not opt.?)
```

</details>

#### option handling 3

- option handling 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option handling 3")

val opt = Some(100)
val result = opt ?? 0
check(result == 100)
```

</details>

#### option handling 4

- option handling 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option handling 4")

val opt = nil
val result = opt ?? 99
check(result == 99)
```

</details>

#### error path 1

- error path 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path 1")

val opt = nil
if opt.?:
    check(false)
else:
    check(true)
```

</details>

#### error path 2

- error path 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path 2")

val arr = []
check(arr.len() == 0)
```

</details>

#### error path 3

- error path 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path 3")

var error = nil
check(error == nil)
```

</details>

#### edge case 1 - empty

- edge case 1 - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 1 - empty")

val s = ""
check(s.len() == 0)
```

</details>

#### edge case 2 - zero

- edge case 2 - zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 2 - zero")

check(0 == 0)
check(not (0 > 0))
```

</details>

#### edge case 3 - negative

- edge case 3 - negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 3 - negative")

check(-1 < 0)
```

</details>

#### edge case 4 - large

- edge case 4 - large


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 4 - large")

check(999999 > 0)
```

</details>

#### edge case 5 - single element

- edge case 5 - single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 5 - single element")

val arr = [1]
check(arr.len() == 1)
```

</details>

#### boundary 1 - min

- boundary 1 - min


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boundary 1 - min")

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### boundary 2 - max

- boundary 2 - max


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boundary 2 - max")

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### conditional 1

- conditional 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional 1")

if true:
    check(true)
else:
    check(false)
```

</details>

#### conditional 2

- conditional 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional 2")

val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### conditional 3

- conditional 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional 3")

val x = 3
if x > 10:
    check(false)
elif x > 5:
    check(false)
else:
    check(true)
```

</details>

<details>
<summary>Advanced: loop 1 - for</summary>

#### loop 1 - for

- loop 1 - for


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop 1 - for")

var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>


</details>

<details>
<summary>Advanced: loop 2 - while</summary>

#### loop 2 - while

- loop 2 - while


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop 2 - while")

var count = 0
while count < 5:
    count = count + 1
check(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: loop 3 - break</summary>

#### loop 3 - break

- loop 3 - break


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop 3 - break")

var count = 0
for i in 0..100:
    count = count + 1
    if count == 5:
        break
check(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: loop 4 - continue</summary>

#### loop 4 - continue

- loop 4 - continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop 4 - continue")

var executed = 0
for i in 0..10:
    if i % 2 == 0:
        continue
    executed = executed + 1
check(executed == 5)
```

</details>


</details>

#### match 1

- match 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 1")

val opt = Some(1)
match opt:
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

#### match 2

- match 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 2")

val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### match 3

- match 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 3")

val value = 2
val result = match value:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "two")
```

</details>

#### nested 1

- nested 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested 1")

if true:
    if true:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### nested 2

- nested 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested 2")

for i in 0..3:
    for j in 0..3:
        check(i >= 0 and j >= 0)
```

</details>

#### complex 1

- complex 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex 1")

val arr = [1, 2, 3, 4, 5]
var result = []
for x in arr:
    if x % 2 == 0:
        result = result.append(x * 2)
check(result.len() == 2)
```

</details>

#### complex 2

- complex 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex 2")

val dict = {"a": 1, "b": 2, "c": 3}
check(dict["a"] == 1)
check(dict["b"] == 2)
check(dict["c"] == 3)
```

</details>

#### integration 1

- integration 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integration 1")

val data = [1, 2, 3]
var processed = []
for x in data:
    processed = processed.append(x * 2)
var sum = 0
for x in processed:
    sum = sum + x
check(sum == 12)
```

</details>

#### integration 2

- integration 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integration 2")

val input = "test"
val stage1 = input + "_1"
val stage2 = stage1 + "_2"
val stage3 = stage2 + "_3"
check(stage3 == "test_1_2_3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `8f0f06cf2f88b3641e9ba539ad6b0813bf8a08beb1267eb1f206c9305b36f1b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f0f06cf2f88b3641e9ba539ad6b0813bf8a08beb1267eb1f206c9305b36f1b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f0f06cf2f88b3641e9ba539ad6b0813bf8a08beb1267eb1f206c9305b36f1b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/std/improved/list_integration_spec.spl
mirror: doc/06_spec/unit/std/improved/list_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/improved/list_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/improved/list_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/improved/list_integration_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic operation 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/improved/list_integration_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic operation 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/improved/list_integration_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic operation 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
