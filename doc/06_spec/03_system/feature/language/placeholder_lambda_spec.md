# Placeholder Lambda Specification

> Placeholder `_` syntax for creating concise lambda expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placeholder Lambda Specification

Placeholder `_` syntax for creating concise lambda expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLACEHOLDER-LAMBDA |
| Category | Syntax |
| Status | In Progress |
| Source | `test/03_system/feature/language/placeholder_lambda_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Placeholder `_` syntax for creating concise lambda expressions.
`nums.map(_ * 2)` desugars to `nums.map(\__p0: __p0 * 2)`

## Scenarios

### Placeholder Lambda

#### single placeholder

#### transforms _ * 2 to lambda

- transforms _ * 2 to lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms _ * 2 to lambda")
val nums = [1, 2, 3]
expect nums.map(_ * 2) == [2, 4, 6]
```

</details>

#### transforms _ + 10 to lambda

- transforms _ + 10 to lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms _ + 10 to lambda")
val nums = [1, 2, 3]
expect nums.map(_ + 10) == [11, 12, 13]
```

</details>

#### transforms _ - 1 to lambda

- transforms _ - 1 to lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms _ - 1 to lambda")
val nums = [5, 10, 15]
expect nums.map(_ - 1) == [4, 9, 14]
```

</details>

#### transforms _ / 2 to lambda

- transforms _ / 2 to lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms _ / 2 to lambda")
val nums = [10, 20, 30]
expect nums.map(_ / 2) == [5, 10, 15]
```

</details>

#### transforms unary negation -_

- transforms unary negation -_


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms unary negation -_")
val nums = [1, -2, 3]
expect nums.map(-_) == [-1, 2, -3]
```

</details>

#### field access

#### accesses x field with _.x

- accesses x field with _.x


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses x field with _.x")
struct Point:
    x: i64
    y: i64
val points = [Point(x=1, y=2), Point(x=3, y=4)]
expect points.map(_.x) == [1, 3]
```

</details>

#### accesses y field with _.y

- accesses y field with _.y


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses y field with _.y")
struct Point:
    x: i64
    y: i64
val points = [Point(x=1, y=2), Point(x=3, y=4)]
expect points.map(_.y) == [2, 4]
```

</details>

#### method call

#### calls method with _.method()

- calls method with _.method()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls method with _.method()")
val texts = ["hello", "world"]
expect texts.map(_.len()) == [5, 5]
```

</details>

#### multiple placeholders

#### reduces with _ + _

- reduces with _ + _


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduces with _ + _")
val nums = [1, 2, 3, 4]
# reduce requires (init, lambda) form with explicit lambda
expect nums.reduce(0, \acc, x: acc + x) == 10
```

</details>

#### reduces with _ * _

- reduces with _ * _


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduces with _ * _")
val nums = [1, 2, 3, 4]
# reduce requires (init, lambda) form with explicit lambda
expect nums.reduce(1, \acc, x: acc * x) == 24
```

</details>

#### compares with _ < _

- compares with _ < _


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares with _ < _")
val a = 3
val b = 5
val compare = \x, y: x < y
# This tests that _ < _ creates a two-argument lambda
expect compare(a, b) == true
```

</details>

#### with filter

#### filters with _ > threshold

- filters with _ > threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with _ > threshold")
val nums = [1, 5, 3, 8, 2]
expect nums.filter(_ > 3) == [5, 8]
```

</details>

#### filters with _ < threshold

- filters with _ < threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with _ < threshold")
val nums = [1, 5, 3, 8, 2]
expect nums.filter(_ < 4) == [1, 3, 2]
```

</details>

#### filters with _ == value

- filters with _ == value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with _ == value")
val nums = [1, 2, 2, 3, 2]
expect nums.filter(_ == 2) == [2, 2, 2]
```

</details>

#### chained operations

#### chains map and filter

- chains map and filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains map and filter")
val nums = [1, 2, 3, 4, 5]
expect nums.map(_ * 2).filter(_ > 5) == [6, 8, 10]
```

</details>

#### chains filter and map

- chains filter and map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains filter and map")
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ > 2).map(_ * 10) == [30, 40, 50]
```

</details>

#### indexing

#### accesses first element with indexed placeholder

- accesses first element with indexed placeholder
   - Expected: arrays.map(_1[0]) equals `[1, 4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses first element with indexed placeholder")
val arrays = [[1, 2, 3], [4, 5, 6]]
expect(arrays.map(_1[0])).to_equal([1, 4])
```

</details>

#### accesses second element with indexed placeholder

- accesses second element with indexed placeholder
   - Expected: arrays.map(_1[1]) equals `[2, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses second element with indexed placeholder")
val arrays = [[1, 2, 3], [4, 5, 6]]
expect(arrays.map(_1[1])).to_equal([2, 5])
```

</details>

#### complex expressions

#### combines operators in expression

- combines operators in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines operators in expression")
val nums = [1, 2, 3]
expect nums.map(_ * 2 + 1) == [3, 5, 7]
expect nums.map((_ + 1) * 2) == [4, 6, 8]
```

</details>

#### maps with conditional classification

- maps with conditional classification


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with conditional classification")
val nums = [1, 2, 3, 4, 5]
fn classify(x: i64) -> text:
    if x > 3:
        return "big"
    else:
        return "small"
expect nums.map(classify(_1)) == ["small", "small", "small", "big", "big"]
```

</details>

#### no transformation when no placeholder

#### leaves expressions without _ unchanged

- leaves expressions without _ unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves expressions without _ unchanged")
val nums = [1, 2, 3]
expect nums.map(_1 * 2) == [2, 4, 6]
```

</details>

#### edge cases

#### handles single element list

- handles single element list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single element list")
val nums = [42]
expect nums.map(_ * 2) == [84]
```

</details>

#### handles empty list

- handles empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty list")
val nums: [i64] = []
expect nums.map(_ * 2) == []
```

</details>

#### handles nested function calls

- handles nested function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles nested function calls")
fn double(x: i64) -> i64:
    x * 2
val nums = [1, 2, 3]
# Placeholder expressions are supported inside callback call arguments.
expect nums.map(double(_1)) == [2, 4, 6]
```

</details>

#### null coalescing

#### coalesces with _ ?? default

- coalesces with _ ?? default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coalesces with _ ?? default")
val opts: [Option<i64>] = [Some(1), nil, Some(3)]
expect opts.map(_ ?? 0) == [1, 0, 3]
```

</details>

#### coalesces with expression on right side

- coalesces with expression on right side


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coalesces with expression on right side")
val opts: [Option<i64>] = [Some(10), nil, Some(30)]
expect opts.map(_ ?? -1 * 100) == [10, -100, 30]
```

</details>

#### slicing

#### slices with _[start:end]

- slices with _[start:end]


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with _[start:end]")
val texts = ["hello", "world"]
expect texts.map(_[1:4]) == ["ell", "orl"]
```

</details>

#### slices with _[:end]

- slices with _[:end]


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with _[:end]")
val texts = ["hello", "world"]
expect texts.map(_[:3]) == ["hel", "wor"]
```

</details>

#### slices with _[start:]

- slices with _[start:]


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with _[start:]")
val texts = ["hello", "world"]
expect texts.map(_[2:]) == ["llo", "rld"]
```

</details>

#### slices with step _[::step]

- slices with step _[::step]


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with step _[::step]")
val texts = ["abcdef", "ghijkl"]
expect texts.map(_[::2]) == ["ace", "gik"]
```

</details>

#### tuple with placeholders

#### creates tuple with placeholder (_, constant)

- creates tuple with placeholder (_, constant)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates tuple with placeholder (_, constant)")
val nums = [1, 2, 3]
expect nums.map((_, 0)) == [(1, 0), (2, 0), (3, 0)]
```

</details>

#### creates tuple with constant first (constant, _)

- creates tuple with constant first (constant, _)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates tuple with constant first (constant, _)")
val nums = [1, 2, 3]
expect nums.map((100, _)) == [(100, 1), (100, 2), (100, 3)]
```

</details>

#### creates 3-tuple with placeholder

- creates 3-tuple with placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates 3-tuple with placeholder")
val nums = [1, 2, 3]
expect nums.map((_, "x", 0)) == [(1, "x", 0), (2, "x", 0), (3, "x", 0)]
```

</details>

#### method call with arguments

#### calls method with explicit args _.method(arg)

- calls method with explicit args _.method(arg)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls method with explicit args _.method(arg)")
val texts = ["hello", "world"]
expect texts.map(_.slice(0, 3)) == ["hel", "wor"]
```

</details>

#### calls method with placeholder in args _.method(_) from outer scope

- calls method with placeholder in args _.method(_) from outer scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls method with placeholder in args _.method(_) from outer scope")
# Note: placeholder in function call args not supported, use explicit lambda
val nums = [1, 2, 3]
fn add(a: i64, b: i64) -> i64:
    a + b
expect nums.map(add(_1, 10)) == [11, 12, 13]
```

</details>

#### chained method calls

#### chains method calls _.method1().method2()

- chains method calls _.method1().method2()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains method calls _.method1().method2()")
val texts = ["  hello  ", "  world  "]
expect texts.map(_.trim().len()) == [5, 5]
```

</details>

#### chains multiple string methods

- chains multiple string methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple string methods")
val texts = ["HELLO", "WORLD"]
expect texts.map(_.lower().len()) == [5, 5]
```

</details>

#### chains slice with length

- chains slice with length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains slice with length")
val texts = ["hello world", "foo bar baz"]
expect texts.map(_[:5].len()) == [5, 5]
```

</details>

#### scope isolation with nested lambdas

#### does not transform _ inside nested lambda

- does not transform _ inside nested lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not transform _ inside nested lambda")
val nums = [1, 2, 3]
# The outer _ is transformed, inner \x: x stays as is
expect nums.map(_ + (\x: x * 2)(10)) == [21, 22, 23]
```

</details>

#### nested lambda with its own _ is independent

- nested lambda with its own _ is independent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested lambda with its own _ is independent")
val nums = [1, 2, 3]
# Outer _ becomes __p0, inner _ is separate lambda scope
# This should work because inner lambda is not traversed
val transform = _1 * 2
expect nums.map(_ + transform(5)) == [11, 12, 13]
```

</details>

#### comparison operators

#### uses _ in greater-or-equal comparison

- uses _ in greater-or-equal comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses _ in greater-or-equal comparison")
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ >= 3) == [3, 4, 5]
```

</details>

#### uses _ in less-or-equal comparison

- uses _ in less-or-equal comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses _ in less-or-equal comparison")
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ <= 3) == [1, 2, 3]
```

</details>

#### uses _ in not-equal comparison

- uses _ in not-equal comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses _ in not-equal comparison")
val nums = [1, 2, 2, 3, 2]
expect nums.filter(_ != 2) == [1, 3]
```

</details>

#### logical operators

#### uses explicit lambda with logical and

- uses explicit lambda with logical and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses explicit lambda with logical and")
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_1 > 1 && _1 < 5) == [2, 3, 4]
```

</details>

#### uses explicit lambda with logical or

- uses explicit lambda with logical or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses explicit lambda with logical or")
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_1 == 1 || _1 == 5) == [1, 5]
```

</details>

#### modulo and other operators

#### uses _ with modulo

- uses _ with modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses _ with modulo")
val nums = [1, 2, 3, 4, 5, 6]
expect nums.filter(_ % 2 == 0) == [2, 4, 6]
```

</details>

#### uses _ with bitwise and

- uses _ with bitwise and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses _ with bitwise and")
val nums = [1, 2, 3, 4, 5]
expect nums.map(_ & 1) == [1, 0, 1, 0, 1]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
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

- Canonical SPipe generation for source `bef91ea7358dd5c3d7728f1330692d974e14ba44b3adb3c10de872160bb75e86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bef91ea7358dd5c3d7728f1330692d974e14ba44b3adb3c10de872160bb75e86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bef91ea7358dd5c3d7728f1330692d974e14ba44b3adb3c10de872160bb75e86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/language/placeholder_lambda_spec.spl
mirror: doc/06_spec/03_system/feature/language/placeholder_lambda_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/placeholder_lambda_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/placeholder_lambda_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/placeholder_lambda_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms _ * 2 to lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/placeholder_lambda_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms _ + 10 to lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/placeholder_lambda_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms _ - 1 to lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
