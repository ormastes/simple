# Error Path System Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Path System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ERROR |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/core/error_path/error_path_99_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Error Path Coverage

<details>
<summary>Advanced: error path 1 - null check</summary>

#### error path 1 - null check _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- error path 1 - null check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 1 - null check")
val opt_val = nil
if opt_val.?:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 2 - empty check</summary>

#### error path 2 - empty check _(slow)_

- error path 2 - empty check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 2 - empty check")
val arr = []
if arr.len() > 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 3 - negative check</summary>

#### error path 3 - negative check _(slow)_

- error path 3 - negative check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 3 - negative check")
val num = -1
if num >= 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 4 - zero check</summary>

#### error path 4 - zero check _(slow)_

- error path 4 - zero check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 4 - zero check")
val num = 0
if num > 0:
    verify(false)
elif num < 0:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 5 - option unwrap fail</summary>

#### error path 5 - option unwrap fail _(slow)_

- error path 5 - option unwrap fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 5 - option unwrap fail")
val opt = nil
val result = opt ?? "default"
verify(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: error path 6 - dict missing key</summary>

#### error path 6 - dict missing key _(slow)_

- error path 6 - dict missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 6 - dict missing key")
val d = {"key": "value"}
val result = d.get("missing")
verify(not result.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 7 - array out of bounds protection</summary>

#### error path 7 - array out of bounds protection _(slow)_

- error path 7 - array out of bounds protection


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 7 - array out of bounds protection")
val arr = [1, 2, 3]
val safe_len = arr.len()
verify(safe_len == 3)
```

</details>


</details>

<details>
<summary>Advanced: error path 8 - string empty slice</summary>

#### error path 8 - string empty slice _(slow)_

- error path 8 - string empty slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 8 - string empty slice")
val s = "test"
val slice = s[0..0]
verify(slice.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 9 - comparison false path</summary>

#### error path 9 - comparison false path _(slow)_

- error path 9 - comparison false path


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 9 - comparison false path")
val a = 5
val b = 10
if a > b:
    verify(false)
elif a == b:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 10 - match default</summary>

#### error path 10 - match default _(slow)_

- error path 10 - match default


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 10 - match default")
val value = 999
val result = match value:
    1: "one"
    2: "two"
    _: "default"
verify(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: error path 11 - loop never executes</summary>

#### error path 11 - loop never executes _(slow)_

- error path 11 - loop never executes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 11 - loop never executes")
var count = 0
while false:
    count = count + 1
verify(count == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 12 - for loop empty range</summary>

#### error path 12 - for loop empty range _(slow)_

- error path 12 - for loop empty range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 12 - for loop empty range")
var sum = 0
for i in 10..10:
    sum = sum + i
verify(sum == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 13 - nested nil check</summary>

#### error path 13 - nested nil check _(slow)_

- error path 13 - nested nil check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 13 - nested nil check")
val opt1 = nil
val opt2 = opt1 ?? nil
verify(not opt2.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 14 - boolean false branch</summary>

#### error path 14 - boolean false branch _(slow)_

- error path 14 - boolean false branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 14 - boolean false branch")
val cond = false
if cond and true:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 15 - or first false</summary>

#### error path 15 - or first false _(slow)_

- error path 15 - or first false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 15 - or first false")
val result = false or true
verify(result)
```

</details>


</details>

<details>
<summary>Advanced: error path 16 - and first false</summary>

#### error path 16 - and first false _(slow)_

- error path 16 - and first false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 16 - and first false")
val result = false and true
verify(not result)
```

</details>


</details>

<details>
<summary>Advanced: error path 17 - not operation</summary>

#### error path 17 - not operation _(slow)_

- error path 17 - not operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 17 - not operation")
verify(not false)
verify(not (not true))
```

</details>


</details>

<details>
<summary>Advanced: error path 18 - empty string operations</summary>

#### error path 18 - empty string operations _(slow)_

- error path 18 - empty string operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 18 - empty string operations")
val s = ""
verify(not s.contains("x"))
verify(s.starts_with(""))
verify(s.ends_with(""))
```

</details>


</details>

<details>
<summary>Advanced: error path 19 - zero division protection</summary>

#### error path 19 - zero division protection _(slow)_

- error path 19 - zero division protection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 19 - zero division protection")
val denom = 1  # Ensure non-zero
if denom != 0:
    val result = 10 / denom
    verify(result == 10)
else:
    verify(false)
```

</details>


</details>

<details>
<summary>Advanced: error path 20 - negative index</summary>

#### error path 20 - negative index _(slow)_

- error path 20 - negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 20 - negative index")
val arr = [1, 2, 3]
val last = arr[-1]
verify(last == 3)
```

</details>


</details>

<details>
<summary>Advanced: error path 21 - break immediately</summary>

#### error path 21 - break immediately _(slow)_

- error path 21 - break immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 21 - break immediately")
var count = 1
verify(count == 1)
```

</details>


</details>

<details>
<summary>Advanced: error path 22 - continue all</summary>

#### error path 22 - continue all _(slow)_

- error path 22 - continue all


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 22 - continue all")
var pre_continue = 5
var post_continue = 0
verify(pre_continue == 5)
verify(post_continue == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 23 - multiple elif failures</summary>

#### error path 23 - multiple elif failures _(slow)_

- error path 23 - multiple elif failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 23 - multiple elif failures")
val x = 100
if x < 10:
    verify(false)
elif x < 50:
    verify(false)
elif x < 75:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 24 - match all patterns fail to default</summary>

#### error path 24 - match all patterns fail to default _(slow)_

- error path 24 - match all patterns fail to default


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 24 - match all patterns fail to default")
val value = "unknown"
val result = match value:
    "a": 1
    "b": 2
    "c": 3
    _: 0
verify(result == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 25 - nested loops early exit</summary>

#### error path 25 - nested loops early exit _(slow)_

- error path 25 - nested loops early exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 25 - nested loops early exit")
var count = 5
verify(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: error path 26 - comparison chain all false</summary>

#### error path 26 - comparison chain all false _(slow)_

- error path 26 - comparison chain all false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 26 - comparison chain all false")
val x = 100
if x < 10 or x > 200:
    verify(false)
else:
    verify(true)
```

</details>


</details>

<details>
<summary>Advanced: error path 27 - option chain breaks</summary>

#### error path 27 - option chain breaks _(slow)_

- error path 27 - option chain breaks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 27 - option chain breaks")
val opt = Some(nil)
verify(not opt.?)
```

</details>


</details>

<details>
<summary>Advanced: error path 28 - arithmetic bounds</summary>

#### error path 28 - arithmetic bounds _(slow)_

- error path 28 - arithmetic bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 28 - arithmetic bounds")
val large = 1000000
val result = large + 1
verify(result > large)
```

</details>


</details>

<details>
<summary>Advanced: error path 29 - string concatenation empty</summary>

#### error path 29 - string concatenation empty _(slow)_

- error path 29 - string concatenation empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 29 - string concatenation empty")
val s1 = ""
val s2 = ""
val result = s1 + s2
verify(result.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: error path 30 - array filter all fail</summary>

#### error path 30 - array filter all fail _(slow)_

- error path 30 - array filter all fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path 30 - array filter all fail")
val arr = [1, 2, 3, 4, 5]
var filtered = []
for x in arr:
    if x > 10:
        filtered = filtered.append(x)
verify(filtered.len() == 0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 30 |
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

- Canonical SPipe generation for source `072b3e7ce1b2d413622341e2c8f98b291fcf3278cb97c3bec67150292fa9184b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `072b3e7ce1b2d413622341e2c8f98b291fcf3278cb97c3bec67150292fa9184b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `072b3e7ce1b2d413622341e2c8f98b291fcf3278cb97c3bec67150292fa9184b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/core/error_path/error_path_99_system_spec.spl
mirror: doc/06_spec/03_system/core/error_path/error_path_99_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/core/error_path/error_path_99_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/core/error_path/error_path_99_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/core/error_path/error_path_99_system_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'error path 1 - null check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/core/error_path/error_path_99_system_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'error path 2 - empty check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/core/error_path/error_path_99_system_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'error path 3 - negative check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
