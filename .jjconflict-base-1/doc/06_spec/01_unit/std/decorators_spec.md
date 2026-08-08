# Decorators Specification

> 1. fn square

<!-- sdn-diagram:id=decorators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=decorators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

decorators_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=decorators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorators Specification

## Scenarios

### CachedFunction wrapper

#### caches function results

1. fn square
   - Expected: result1 equals `25`
   - Expected: result2 equals `25`
   - Expected: info["hits"] equals `1`
   - Expected: info["misses"] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x):
    return x * x

# Create cached version
val wrapper = cached(square)

# First call should miss cache
val result1 = wrapper.__call__(5)
expect(result1).to_equal(25)

# Second call should hit cache
val result2 = wrapper.__call__(5)
expect(result2).to_equal(25)

# Check cache stats
val info = wrapper.cache_info()
expect(info["hits"]).to_equal(1)
expect(info["misses"]).to_equal(1)
```

</details>

#### caches different arguments separately

1. fn add
   - Expected: result1 equals `5`
   - Expected: result2 equals `9`
   - Expected: result3 equals `5`
   - Expected: info["hits"] equals `1`
   - Expected: info["misses"] equals `2`
   - Expected: info["size"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    return a + b

val wrapper = cached(add)

val result1 = wrapper.__call__(2, 3)
expect(result1).to_equal(5)

val result2 = wrapper.__call__(4, 5)
expect(result2).to_equal(9)

val result3 = wrapper.__call__(2, 3)
expect(result3).to_equal(5)

val info = wrapper.cache_info()
expect(info["hits"]).to_equal(1)
expect(info["misses"]).to_equal(2)
expect(info["size"]).to_equal(2)
```

</details>

#### clears cache correctly

1. fn double
2. wrapper   call
3. wrapper   call
   - Expected: info1["hits"] equals `1`
4. wrapper clear cache
   - Expected: info2["hits"] equals `0`
   - Expected: info2["misses"] equals `0`
   - Expected: info2["size"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    return x * 2

val wrapper = cached(double)

wrapper.__call__(5)
wrapper.__call__(5)

val info1 = wrapper.cache_info()
expect(info1["hits"]).to_equal(1)

wrapper.clear_cache()

val info2 = wrapper.cache_info()
expect(info2["hits"]).to_equal(0)
expect(info2["misses"]).to_equal(0)
expect(info2["size"]).to_equal(0)
```

</details>

### LoggedFunction wrapper

#### logs function calls

1. fn multiply
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(x, y):
    return x * y

val wrapper = logged(multiply)
val result = wrapper.__call__(3, 4)

# Should log input and output
# Note: output goes to stdout, we just verify it doesn't error
expect(result).to_equal(12)
```

</details>

#### logs return values

1. fn get value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value():
    return 42

val wrapper = logged(get_value)
val result = wrapper.__call__()

expect(result).to_equal(42)
```

</details>

### DeprecatedFunction wrapper

#### shows warning when called

1. fn old api
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn old_api(x):
    return x + 1

val wrapper = deprecated(old_api, "Old API")

# First call should print warning
val result = wrapper.__call__(5)
expect(result).to_equal(6)
```

</details>

#### includes replacement message

1. fn legacy function
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn legacy_function(x):
    return x * 2

val wrapper = deprecated(legacy_function, "Use new_function() instead")

val result = wrapper.__call__(10)
expect(result).to_equal(20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/decorators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CachedFunction wrapper
- LoggedFunction wrapper
- DeprecatedFunction wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
