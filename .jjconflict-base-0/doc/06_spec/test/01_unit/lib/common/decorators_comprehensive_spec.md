# Decorators Comprehensive Specification

> <details>

<!-- sdn-diagram:id=decorators_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=decorators_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

decorators_comprehensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=decorators_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorators Comprehensive Specification

## Scenarios

### CachedFunction Comprehensive Tests

### Basic caching

#### caches 0-argument functions

- fn expensive zero
- var cf = cached
   - Expected: result1 equals `42`
   - Expected: result2 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn expensive_zero():
    return 42

var cf = cached(expensive_zero)
val result1 = call0(cf)
expect(result1).to_equal(42)

val result2 = call0(cf)
expect(result2).to_equal(42)
```

</details>

#### caches 1-argument functions

- fn square
- var cf = cached
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`
   - Expected: result3 equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x):
    return x * x

var cf = cached(square)
val result1 = call1(cf, 5)
expect(result1).to_equal(25)

val result2 = call1(cf, 5)
expect(result2).to_equal(25)

val result3 = call1(cf, 3)
expect(result3).to_equal(9)
```

</details>

#### caches 2-argument functions

- fn add
- var cf = cached
   - Expected: result1 equals `5`
   - Expected: result2 equals `5`
   - Expected: result3 equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    return a + b

var cf = cached(add)
val result1 = call2(cf, 2, 3)
expect(result1).to_equal(5)

val result2 = call2(cf, 2, 3)
expect(result2).to_equal(5)

val result3 = call2(cf, 4, 5)
expect(result3).to_equal(9)
```

</details>

#### caches 3-argument functions

- fn sum3
- var cf = cached
   - Expected: result1 equals `6`
   - Expected: result2 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum3(a, b, c):
    return a + b + c

var cf = cached(sum3)
val result1 = call3(cf, 1, 2, 3)
expect(result1).to_equal(6)

val result2 = call3(cf, 1, 2, 3)
expect(result2).to_equal(6)
```

</details>

### Cache management

#### clears cache correctly

- fn double cache
- var cf = cached
- call1
- call1
- call1
   - Expected: info1["hits"] equals `0`
   - Expected: info1["size"] equals `0`
- cf clear cache
   - Expected: info2["hits"] equals `0`
   - Expected: info2["misses"] equals `0`
   - Expected: info2["size"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn concat
- var cf = cached
   - Expected: result1 equals `12`
   - Expected: result2 equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn returns nil cache
- var cf = cached
   - Expected: result1 equals `nil`
   - Expected: result2 equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn negate
- var cf = cached
   - Expected: result1 equals `5`
   - Expected: result2 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn negate(x):
    return -x

var cf = cached(negate)
val result1 = call1(cf, -5)
expect(result1).to_equal(5)

val result2 = call1(cf, -5)
expect(result2).to_equal(5)
```

</details>

### LoggedFunction Comprehensive Tests

### Basic logging

#### logs 0-argument functions

- fn get value
- var lf = logged
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value():
    return 42

var lf = logged(get_value)
val result = call0(lf)
expect(result).to_equal(42)
```

</details>

#### logs 1-argument functions

- fn double log
- var lf = logged
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_log(x):
    return x * 2

var lf = logged(double_log)
val result = call1(lf, 21)
expect(result).to_equal(42)
```

</details>

#### logs 2-argument functions

- fn multiply
- var lf = logged
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(x, y):
    return x * y

var lf = logged(multiply)
val result = call2(lf, 6, 7)
expect(result).to_equal(42)
```

</details>

#### logs multiple calls

- fn increment
- var lf = logged
   - Expected: result1 equals `2`
   - Expected: result2 equals `3`
   - Expected: result3 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment(x):
    return x + 1

var lf = logged(increment)
val result1 = call1(lf, 1)
val result2 = call1(lf, 2)
val result3 = call1(lf, 3)

expect(result1).to_equal(2)
expect(result2).to_equal(3)
expect(result3).to_equal(4)
```

</details>

### Edge cases

#### logs nil arguments

- fn identity
- var lf = logged
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    return x

var lf = logged(identity)
val result = call1(lf, nil)
expect(result).to_equal(nil)
```

</details>

#### logs nil return values

- fn returns nil log
- var lf = logged
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn old api
- var df = deprecated
   - Expected: result1 equals `6`
   - Expected: result2 equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_api(x):
    return x + 1

var df = deprecated(old_api, "Use new_api() instead")
val result1 = call1(df, 5)
expect(result1).to_equal(6)

val result2 = call1(df, 10)
expect(result2).to_equal(11)
```

</details>

#### handles 0-argument functions

- fn legacy get
- var df = deprecated
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn legacy_get():
    return 99

var df = deprecated(legacy_get, "Old getter")
val result = call0(df)
expect(result).to_equal(99)
```

</details>

#### handles 2-argument functions

- fn old add
- var df = deprecated
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_add(a, b):
    return a + b

var df = deprecated(old_add, "Use operator + instead")
val result = call2(df, 20, 22)
expect(result).to_equal(42)
```

</details>

#### handles multiple arguments

- fn old sum
- var df = deprecated
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_sum(a, b, c):
    return a + b + c

var df = deprecated(old_sum, "Use sum() function")
val result = call3(df, 10, 15, 17)
expect(result).to_equal(42)
```

</details>

### Message handling

#### shows custom message when provided

- fn old func
- var df = deprecated
- call0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_func():
    return 1

var df = deprecated(old_func, "Custom message here")
call0(df)
```

</details>

#### shows default message when no message provided

- fn another old func
- var df = deprecated
- call0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn another_old_func():
    return 2

var df = deprecated(another_old_func, nil)
call0(df)
```

</details>

### Decorator Composition

#### combines caching and logging

- fn expensive compose
- var cf = cached
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn expensive_compose(x):
    return x * x

var cf = cached(expensive_compose)
val result1 = call1(cf, 5)
expect(result1).to_equal(25)

val result2 = call1(cf, 5)
expect(result2).to_equal(25)
```

</details>

#### combines deprecation and caching

- fn old expensive
- var cf = cached
   - Expected: result1 equals `20`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_expensive(x):
    return x * 2

var cf = cached(old_expensive)
val result1 = call1(cf, 10)
expect(result1).to_equal(20)

val result2 = call1(cf, 10)
expect(result2).to_equal(20)
```

</details>

### TimeoutFunction Tests

#### calls function without timeout enforcement

- fn quick func
- var tf = make timeout
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn quick_func(x):
    return x + 1

var tf = make_timeout(quick_func, 5)
val result = call1(tf, 41)
expect(result).to_equal(42)
```

</details>

#### returns TimeoutResult.Success

- fn another func
- var tf = make timeout
   - Expected: result.is_success() is true
   - Expected: result.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn another_func(x):
    return x * 2

var tf = make_timeout(another_func, 5)
val result = call_with_result1(tf, 21)
expect(result.is_success()).to_equal(true)
expect(result.unwrap()).to_equal(42)
```

</details>

### Variadic Argument Forwarding

#### forwards 0 arguments

- fn no args
- var cf = cached
   - Expected: call0(cf) equals `no args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_args():
    return "no args"

var cf = cached(no_args)
expect(call0(cf)).to_equal("no args")
```

</details>

#### forwards 1 argument

- fn one arg
- var cf = cached
   - Expected: call1(cf, 42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn one_arg(x):
    return x

var cf = cached(one_arg)
expect(call1(cf, 42)).to_equal(42)
```

</details>

#### forwards 2 arguments

- fn two args
- var cf = cached
   - Expected: call2(cf, 20, 22) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn two_args(a, b):
    return a + b

var cf = cached(two_args)
expect(call2(cf, 20, 22)).to_equal(42)
```

</details>

#### forwards 3 arguments

- fn three args
- var cf = cached
   - Expected: call3(cf, 10, 15, 17) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn three_args(a, b, c):
    return a + b + c

var cf = cached(three_args)
expect(call3(cf, 10, 15, 17)).to_equal(42)
```

</details>

#### forwards 5 arguments

- fn five args
- var cf = cached
   - Expected: call5(cf, 5, 10, 8, 9, 10) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn five_args(a, b, c, d, e):
    return a + b + c + d + e

var cf = cached(five_args)
expect(call5(cf, 5, 10, 8, 9, 10)).to_equal(42)
```

</details>

#### forwards mixed type arguments

- fn mixed
- var lf = logged
   - Expected: result1 equals `42 is the answer`
   - Expected: result2 equals `The answer is 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/decorators_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CachedFunction Comprehensive Tests
- Basic caching
- Cache management
- Edge cases
- LoggedFunction Comprehensive Tests
- Basic logging
- Edge cases
- DeprecatedFunction Comprehensive Tests
- Warning behavior
- Message handling
- Decorator Composition
- TimeoutFunction Tests
- Variadic Argument Forwarding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
