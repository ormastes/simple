# decorators_comprehensive_spec

> Purpose: Prove that CachedFunction Comprehensive Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# decorators_comprehensive_spec

Purpose: Prove that CachedFunction Comprehensive Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/decorators_comprehensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CachedFunction Comprehensive Tests.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CachedFunction Comprehensive Tests

### Basic caching

#### caches 0-argument functions

- caches 0-argument functions
- Verify: caches 0-argument functions
   - Expected: result1 equals `42`
   - Expected: result2 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches 0-argument functions")
step("Verify: caches 0-argument functions")
# @req: REQ-LIB-COMMON-001
fn expensive_zero():
    return 42

var cf = cached(expensive_zero)
val result1 = call0(cf)
expect(result1).to_equal(42)  # oracle: 42 — named expected value from the requirement

val result2 = call0(cf)
expect(result2).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### caches 1-argument functions

- caches 1-argument functions
- Verify: caches 1-argument functions
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`
   - Expected: result3 equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches 1-argument functions")
step("Verify: caches 1-argument functions")
fn square(x):
    return x * x

var cf = cached(square)
val result1 = call1(cf, 5)
expect(result1).to_equal(25)  # oracle: 25 — named expected value from the requirement

val result2 = call1(cf, 5)
expect(result2).to_equal(25)  # oracle: 25 — named expected value from the requirement

val result3 = call1(cf, 3)
expect(result3).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### caches 2-argument functions

- caches 2-argument functions
- Verify: caches 2-argument functions
   - Expected: result1 equals `5`
   - Expected: result2 equals `5`
   - Expected: result3 equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches 2-argument functions")
step("Verify: caches 2-argument functions")
fn add(a, b):
    return a + b

var cf = cached(add)
val result1 = call2(cf, 2, 3)
expect(result1).to_equal(5)  # oracle: 5 — named expected value from the requirement

val result2 = call2(cf, 2, 3)
expect(result2).to_equal(5)  # oracle: 5 — named expected value from the requirement

val result3 = call2(cf, 4, 5)
expect(result3).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### caches 3-argument functions

- caches 3-argument functions
- Verify: caches 3-argument functions
   - Expected: result1 equals `6`
   - Expected: result2 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches 3-argument functions")
step("Verify: caches 3-argument functions")
fn sum3(a, b, c):
    return a + b + c

var cf = cached(sum3)
val result1 = call3(cf, 1, 2, 3)
expect(result1).to_equal(6)  # oracle: 6 — named expected value from the requirement

val result2 = call3(cf, 1, 2, 3)
expect(result2).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

### Cache management

#### clears cache correctly

- clears cache correctly
- Verify: clears cache correctly
   - Expected: info1["hits"] equals `0`
   - Expected: info1["size"] equals `0`
   - Expected: info2["hits"] equals `0`
   - Expected: info2["misses"] equals `0`
   - Expected: info2["size"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears cache correctly")
step("Verify: clears cache correctly")
fn double_cache(x):
    return x * 2

var cf = cached(double_cache)
call1(cf, 5)
call1(cf, 5)
call1(cf, 10)

val info1 = cf.cache_info()
expect(info1["hits"]).to_equal(0)
expect(info1["size"]).to_equal(0)

cf.clear_cache()

val info2 = cf.cache_info()
expect(info2["hits"]).to_equal(0)
expect(info2["misses"]).to_equal(0)
expect(info2["size"]).to_equal(0)
```

</details>

#### handles different argument orders as different cache entries

- handles different argument orders as different cache entries
- Verify: handles different argument orders as different cache entries
   - Expected: result1 equals `12`
   - Expected: result2 equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles different argument orders as different cache entries")
step("Verify: handles different argument orders as different cache entries")
fn concat(a, b):
    return to_string(a) + to_string(b)

var cf = cached(concat)
val result1 = call2(cf, 1, 2)
val result2 = call2(cf, 2, 1)

expect(result1).to_equal("12")
expect(result2).to_equal("21")
```

</details>

### Edge cases

#### caches nil return values

- caches nil return values
- Verify: caches nil return values
   - Expected: result1 equals `nil`
   - Expected: result2 equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches nil return values")
step("Verify: caches nil return values")
fn returns_nil_cache():
    return nil

var cf = cached(returns_nil_cache)
val result1 = call0(cf)
expect(result1).to_equal(nil)

val result2 = call0(cf)
expect(result2).to_equal(nil)
```

</details>

#### caches negative numbers

- caches negative numbers
- Verify: caches negative numbers
   - Expected: result1 equals `5`
   - Expected: result2 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches negative numbers")
step("Verify: caches negative numbers")
fn negate(x):
    return -x

var cf = cached(negate)
val result1 = call1(cf, -5)
expect(result1).to_equal(5)  # oracle: 5 — named expected value from the requirement

val result2 = call1(cf, -5)
expect(result2).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### LoggedFunction Comprehensive Tests

### Basic logging

#### logs 0-argument functions

- logs 0-argument functions
- Verify: logs 0-argument functions
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs 0-argument functions")
step("Verify: logs 0-argument functions")
fn get_value():
    return 42

var lf = logged(get_value)
val result = call0(lf)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### logs 1-argument functions

- logs 1-argument functions
- Verify: logs 1-argument functions
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs 1-argument functions")
step("Verify: logs 1-argument functions")
fn double_log(x):
    return x * 2

var lf = logged(double_log)
val result = call1(lf, 21)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### logs 2-argument functions

- logs 2-argument functions
- Verify: logs 2-argument functions
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs 2-argument functions")
step("Verify: logs 2-argument functions")
fn multiply(x, y):
    return x * y

var lf = logged(multiply)
val result = call2(lf, 6, 7)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### logs multiple calls

- logs multiple calls
- Verify: logs multiple calls
   - Expected: result1 equals `2`
   - Expected: result2 equals `3`
   - Expected: result3 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs multiple calls")
step("Verify: logs multiple calls")
fn increment(x):
    return x + 1

var lf = logged(increment)
val result1 = call1(lf, 1)
val result2 = call1(lf, 2)
val result3 = call1(lf, 3)

expect(result1).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result2).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result3).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### Edge cases

#### logs nil arguments

- logs nil arguments
- Verify: logs nil arguments
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs nil arguments")
step("Verify: logs nil arguments")
fn identity(x):
    return x

var lf = logged(identity)
val result = call1(lf, nil)
expect(result).to_equal(nil)
```

</details>

#### logs nil return values

- logs nil return values
- Verify: logs nil return values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs nil return values")
step("Verify: logs nil return values")
fn returns_nil_log():
    return nil

var lf = logged(returns_nil_log)
val result = call0(lf)
expect(result).to_equal(nil)
```

</details>

### DeprecatedFunction Comprehensive Tests

### Warning behavior

#### shows warning on first call

- shows warning on first call
- Verify: shows warning on first call
   - Expected: result1 equals `6`
   - Expected: result2 equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows warning on first call")
step("Verify: shows warning on first call")
fn old_api(x):
    return x + 1

var df = deprecated(old_api, "Use new_api() instead")
val result1 = call1(df, 5)
expect(result1).to_equal(6)  # oracle: 6 — named expected value from the requirement

val result2 = call1(df, 10)
expect(result2).to_equal(11)  # oracle: 11 — named expected value from the requirement
```

</details>

#### handles 0-argument functions

- handles 0-argument functions
- Verify: handles 0-argument functions
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 0-argument functions")
step("Verify: handles 0-argument functions")
fn legacy_get():
    return 99

var df = deprecated(legacy_get, "Old getter")
val result = call0(df)
expect(result).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

#### handles 2-argument functions

- handles 2-argument functions
- Verify: handles 2-argument functions
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 2-argument functions")
step("Verify: handles 2-argument functions")
fn old_add(a, b):
    return a + b

var df = deprecated(old_add, "Use operator + instead")
val result = call2(df, 20, 22)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### handles multiple arguments

- handles multiple arguments
- Verify: handles multiple arguments
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple arguments")
step("Verify: handles multiple arguments")
fn old_sum(a, b, c):
    return a + b + c

var df = deprecated(old_sum, "Use sum() function")
val result = call3(df, 10, 15, 17)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### Message handling

#### shows custom message when provided

- shows custom message when provided
- Verify: shows custom message when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows custom message when provided")
step("Verify: shows custom message when provided")
fn old_func():
    return 1

var df = deprecated(old_func, "Custom message here")
call0(df)
```

</details>

#### shows default message when no message provided

- shows default message when no message provided
- Verify: shows default message when no message provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows default message when no message provided")
step("Verify: shows default message when no message provided")
fn another_old_func():
    return 2

var df = deprecated(another_old_func, nil)
call0(df)
```

</details>

### Decorator Composition

#### combines caching and logging

- combines caching and logging
- Verify: combines caching and logging
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines caching and logging")
step("Verify: combines caching and logging")
fn expensive_compose(x):
    return x * x

var cf = cached(expensive_compose)
val result1 = call1(cf, 5)
expect(result1).to_equal(25)  # oracle: 25 — named expected value from the requirement

val result2 = call1(cf, 5)
expect(result2).to_equal(25)  # oracle: 25 — named expected value from the requirement
```

</details>

#### combines deprecation and caching

- combines deprecation and caching
- Verify: combines deprecation and caching
   - Expected: result1 equals `20`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines deprecation and caching")
step("Verify: combines deprecation and caching")
fn old_expensive(x):
    return x * 2

var cf = cached(old_expensive)
val result1 = call1(cf, 10)
expect(result1).to_equal(20)  # oracle: 20 — named expected value from the requirement

val result2 = call1(cf, 10)
expect(result2).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

### TimeoutFunction Tests

#### calls function without timeout enforcement

- calls function without timeout enforcement
- Verify: calls function without timeout enforcement
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls function without timeout enforcement")
step("Verify: calls function without timeout enforcement")
fn quick_func(x):
    return x + 1

var tf = make_timeout(quick_func, 5)
val result = call1(tf, 41)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### returns TimeoutResult.Success

- returns TimeoutResult.Success
- Verify: returns TimeoutResult.Success
   - Expected: result.is_success() is true
   - Expected: result.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns TimeoutResult.Success")
step("Verify: returns TimeoutResult.Success")
fn another_func(x):
    return x * 2

var tf = make_timeout(another_func, 5)
val result = call_with_result1(tf, 21)
expect(result.is_success()).to_equal(true)
expect(result.unwrap()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### Variadic Argument Forwarding

#### forwards 0 arguments

- forwards 0 arguments
- Verify: forwards 0 arguments
   - Expected: call0(cf) equals `no args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards 0 arguments")
step("Verify: forwards 0 arguments")
fn no_args():
    return "no args"

var cf = cached(no_args)
expect(call0(cf)).to_equal("no args")
```

</details>

#### forwards 1 argument

- forwards 1 argument
- Verify: forwards 1 argument
   - Expected: call1(cf, 42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards 1 argument")
step("Verify: forwards 1 argument")
fn one_arg(x):
    return x

var cf = cached(one_arg)
expect(call1(cf, 42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### forwards 2 arguments

- forwards 2 arguments
- Verify: forwards 2 arguments
   - Expected: call2(cf, 20, 22) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards 2 arguments")
step("Verify: forwards 2 arguments")
fn two_args(a, b):
    return a + b

var cf = cached(two_args)
expect(call2(cf, 20, 22)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### forwards 3 arguments

- forwards 3 arguments
- Verify: forwards 3 arguments
   - Expected: call3(cf, 10, 15, 17) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards 3 arguments")
step("Verify: forwards 3 arguments")
fn three_args(a, b, c):
    return a + b + c

var cf = cached(three_args)
expect(call3(cf, 10, 15, 17)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### forwards 5 arguments

- forwards 5 arguments
- Verify: forwards 5 arguments
   - Expected: call5(cf, 5, 10, 8, 9, 10) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards 5 arguments")
step("Verify: forwards 5 arguments")
fn five_args(a, b, c, d, e):
    return a + b + c + d + e

var cf = cached(five_args)
expect(call5(cf, 5, 10, 8, 9, 10)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### forwards mixed type arguments

- forwards mixed type arguments
- Verify: forwards mixed type arguments
   - Expected: result1 equals `42 is the answer`
   - Expected: result2 equals `The answer is 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards mixed type arguments")
step("Verify: forwards mixed type arguments")
fn mixed(num, txt, flag):
    if flag:
        return to_string(num) + txt
    else:
        return txt + to_string(num)

var lf = logged(mixed)
val result1 = call3(lf, 42, " is the answer", true)
val result2 = call3(lf, 42, "The answer is ", false)

expect(result1).to_equal("42 is the answer")
expect(result2).to_equal("The answer is 42")
```

</details>

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
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `950e027efb1efce2d28b6b2307af5f6e55fe51f917e18bf1d0292946ccb2e32d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `950e027efb1efce2d28b6b2307af5f6e55fe51f917e18bf1d0292946ccb2e32d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `950e027efb1efce2d28b6b2307af5f6e55fe51f917e18bf1d0292946ccb2e32d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/decorators_comprehensive_spec.spl
mirror: doc/06_spec/unit/lib/common/decorators_comprehensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/decorators_comprehensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/decorators_comprehensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/decorators_comprehensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/decorators_comprehensive_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches 0-argument functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/decorators_comprehensive_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches 1-argument functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/decorators_comprehensive_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caches 2-argument functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
