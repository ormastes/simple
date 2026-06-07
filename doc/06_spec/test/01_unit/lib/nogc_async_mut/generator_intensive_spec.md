# Generator Intensive Tests

> Intensive tests for generator patterns: yield/next iteration, stateful generators, finite and infinite (bounded) generators, and GeneratorState transitions.

<!-- sdn-diagram:id=generator_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generator_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generator_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generator_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generator Intensive Tests

Intensive tests for generator patterns: yield/next iteration, stateful generators, finite and infinite (bounded) generators, and GeneratorState transitions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for generator patterns: yield/next iteration, stateful generators,
finite and infinite (bounded) generators, and GeneratorState transitions.

## Scenarios

### Generator Creation

#### creates a generator with initial state

1. var g =CountingGenerator new
   - Expected: g.is_complete() is false
   - Expected: g.done is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 5)
expect(g.is_complete()).to_equal(false)
expect(g.done).to_equal(false)
```

</details>

#### new generator has correct initial current value

1. var g =CountingGenerator new
   - Expected: g.current equals `42`
   - Expected: g.done is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(42, 100)
expect(g.current).to_equal(42)
expect(g.done).to_equal(false)
```

</details>

### Generator Next

#### first next yields a value

1. var g =CountingGenerator new
2. var state = g next
   - Expected: state.is_yielded() is true
   - Expected: state.get_value() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 5)
var state = g.next()
expect(state.is_yielded()).to_equal(true)
expect(state.get_value()).to_equal(1)
```

</details>

#### subsequent nexts yield incremented values

1. var g =CountingGenerator new
2. var s1 = g next
3. var s2 = g next
4. var s3 = g next
   - Expected: s1.get_value() equals `1`
   - Expected: s2.get_value() equals `2`
   - Expected: s3.get_value() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 10)
var s1 = g.next()
var s2 = g.next()
var s3 = g.next()
expect(s1.get_value()).to_equal(1)
expect(s2.get_value()).to_equal(2)
expect(s3.get_value()).to_equal(3)
```

</details>

### Counting Generator

#### counts from 1 up to N then completes

1. var g =CountingGenerator new
2. var vals = collect counting
   - Expected: vals.len() equals `4`
   - Expected: vals[0] equals `1`
   - Expected: vals[1] equals `2`
   - Expected: vals[2] equals `3`
   - Expected: vals[3] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 4)
var vals = collect_counting(g, 100)
expect(vals.len()).to_equal(4)
expect(vals[0]).to_equal(1)
expect(vals[1]).to_equal(2)
expect(vals[2]).to_equal(3)
expect(vals[3]).to_equal(4)
```

</details>

#### is_complete returns true after exhaustion

1. var g =CountingGenerator new
2. var v1 = g next
3. var v2 = g next
   - Expected: g.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 2)
var v1 = g.next()
var v2 = g.next()
expect(g.is_complete()).to_equal(true)
```

</details>

### Fibonacci Generator

#### yields fibonacci sequence

1. var fib = FibGenerator new
2. var vals = collect fib
   - Expected: vals.len() equals `7`
   - Expected: vals[0] equals `1`
   - Expected: vals[1] equals `1`
   - Expected: vals[2] equals `2`
   - Expected: vals[3] equals `3`
   - Expected: vals[4] equals `5`
   - Expected: vals[5] equals `8`
   - Expected: vals[6] equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fib = FibGenerator.new(7)
var vals = collect_fib(fib, 100)
expect(vals.len()).to_equal(7)
expect(vals[0]).to_equal(1)
expect(vals[1]).to_equal(1)
expect(vals[2]).to_equal(2)
expect(vals[3]).to_equal(3)
expect(vals[4]).to_equal(5)
expect(vals[5]).to_equal(8)
expect(vals[6]).to_equal(13)
```

</details>

#### fibonacci generator completes after requested count

1. var fib = FibGenerator new
2. var v1 = fib next
3. var v2 = fib next
4. var v3 = fib next
   - Expected: fib.is_complete() is true
5. var v4 = fib next
   - Expected: v4.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fib = FibGenerator.new(3)
var v1 = fib.next()
var v2 = fib.next()
var v3 = fib.next()
expect(fib.is_complete()).to_equal(true)
var v4 = fib.next()
expect(v4.is_completed()).to_equal(true)
```

</details>

### Range Generator

#### yields values in range [start, end)

1. var g =RangeGenerator new
2. var vals = collect range
   - Expected: vals.len() equals `4`
   - Expected: vals[0] equals `3`
   - Expected: vals[1] equals `4`
   - Expected: vals[2] equals `5`
   - Expected: vals[3] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =RangeGenerator.new(3, 7)
var vals = collect_range(g, 100)
expect(vals.len()).to_equal(4)
expect(vals[0]).to_equal(3)
expect(vals[1]).to_equal(4)
expect(vals[2]).to_equal(5)
expect(vals[3]).to_equal(6)
```

</details>

### Single Value Generator

#### yields one value then completes

1. var g =SingleValueGenerator new
2. var state = g next
   - Expected: state.is_yielded() is true
   - Expected: state.get_value() equals `99`
   - Expected: g.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =SingleValueGenerator.new(99)
var state = g.next()
expect(state.is_yielded()).to_equal(true)
expect(state.get_value()).to_equal(99)
expect(g.is_complete()).to_equal(true)
```

</details>

#### next after single value returns Completed

1. var g =SingleValueGenerator new
2. var s1 = g next
3. var s2 = g next
   - Expected: s1.is_yielded() is true
   - Expected: s2.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =SingleValueGenerator.new(42)
var s1 = g.next()
var s2 = g.next()
expect(s1.is_yielded()).to_equal(true)
expect(s2.is_completed()).to_equal(true)
```

</details>

### Empty Generator

#### is immediately complete

1. var g =EmptyGenerator new
   - Expected: g.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =EmptyGenerator.new()
expect(g.is_complete()).to_equal(true)
```

</details>

#### next on empty generator returns Completed

1. var g =EmptyGenerator new
2. var state = g next
   - Expected: state.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =EmptyGenerator.new()
var state = g.next()
expect(state.is_completed()).to_equal(true)
```

</details>

### GeneratorState

#### Yielded state has a value

1. var state = GeneratorState Yielded
   - Expected: state.is_yielded() is true
   - Expected: state.get_value() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = GeneratorState.Yielded(value: 10)
expect(state.is_yielded()).to_equal(true)
expect(state.get_value()).to_equal(10)
```

</details>

#### Completed state has no value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = GeneratorState.Completed
expect(state.is_completed()).to_equal(true)
expect(state.get_value()).to_equal(0)
```

</details>

#### is_yielded returns false for Completed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = GeneratorState.Completed
expect(state.is_yielded()).to_equal(false)
```

</details>

#### is_completed returns false for Yielded

1. var state = GeneratorState Yielded
   - Expected: state.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = GeneratorState.Yielded(value: 5)
expect(state.is_completed()).to_equal(false)
```

</details>

### Collect Helper

#### collects all values from generator into list

1. var g =CountingGenerator new
2. var vals = collect counting
   - Expected: vals.len() equals `3`
   - Expected: vals[0] equals `1`
   - Expected: vals[1] equals `2`
   - Expected: vals[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 3)
var vals = collect_counting(g, 100)
expect(vals.len()).to_equal(3)
expect(vals[0]).to_equal(1)
expect(vals[1]).to_equal(2)
expect(vals[2]).to_equal(3)
```

</details>

#### respects max_items limit

1. var g =CountingGenerator new
2. var vals = collect counting
   - Expected: vals.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =CountingGenerator.new(0, 100)
var vals = collect_counting(g, 5)
expect(vals.len()).to_equal(5)
```

</details>

### Generator After Completion

#### next after complete returns Completed

1. var g =SingleValueGenerator new
2. var s1 = g next
3. var s2 = g next
4. var s3 = g next
   - Expected: s1.is_yielded() is true
   - Expected: s2.is_completed() is true
   - Expected: s3.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =SingleValueGenerator.new(7)
var s1 = g.next()
var s2 = g.next()
var s3 = g.next()
expect(s1.is_yielded()).to_equal(true)
expect(s2.is_completed()).to_equal(true)
expect(s3.is_completed()).to_equal(true)
```

</details>

#### calling next many times after completion is safe

1. var g =EmptyGenerator new
2. var state = g next
   - Expected: state.is_completed() is true
   - Expected: g.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =EmptyGenerator.new()
var i = 0
while i < 20:
    var state = g.next()
    expect(state.is_completed()).to_equal(true)
    i = i + 1
expect(g.is_complete()).to_equal(true)
```

</details>

### Transform Generator

#### multiplies each yielded value

1. var source = CountingGenerator new
2. var doubled = DoublingGenerator new
3. var vals = collect doubling
   - Expected: vals.len() equals `4`
   - Expected: vals[0] equals `2`
   - Expected: vals[1] equals `4`
   - Expected: vals[2] equals `6`
   - Expected: vals[3] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = CountingGenerator.new(0, 4)
var doubled = DoublingGenerator.new(source)
var vals = collect_doubling(doubled, 100)
expect(vals.len()).to_equal(4)
expect(vals[0]).to_equal(2)
expect(vals[1]).to_equal(4)
expect(vals[2]).to_equal(6)
expect(vals[3]).to_equal(8)
```

</details>

#### applies identity transform preserving values

1. var source = CountingGenerator new
2. var identity = IdentityGenerator new
3. var vals = collect identity
   - Expected: vals[0] equals `1`
   - Expected: vals[1] equals `2`
   - Expected: vals[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = CountingGenerator.new(0, 3)
var identity = IdentityGenerator.new(source)
var vals = collect_identity(identity, 100)
expect(vals[0]).to_equal(1)
expect(vals[1]).to_equal(2)
expect(vals[2]).to_equal(3)
```

</details>

### Filter Generator

#### skips values not matching predicate

1. var source = CountingGenerator new
2. var evens = EvenFilterGenerator new
3. var vals = collect even filter
   - Expected: vals.len() equals `5`
   - Expected: vals[0] equals `2`
   - Expected: vals[1] equals `4`
   - Expected: vals[2] equals `6`
   - Expected: vals[3] equals `8`
   - Expected: vals[4] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = CountingGenerator.new(0, 10)
var evens = EvenFilterGenerator.new(source)
var vals = collect_even_filter(evens, 100)
# Values 1..10, evens are 2, 4, 6, 8, 10
expect(vals.len()).to_equal(5)
expect(vals[0]).to_equal(2)
expect(vals[1]).to_equal(4)
expect(vals[2]).to_equal(6)
expect(vals[3]).to_equal(8)
expect(vals[4]).to_equal(10)
```

</details>

#### filter with always-true predicate keeps all values

1. var source = CountingGenerator new
2. var all = PassAllFilterGenerator new
3. var vals = collect pass all
   - Expected: vals.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = CountingGenerator.new(0, 3)
var all = PassAllFilterGenerator.new(source)
var vals = collect_pass_all(all, 100)
expect(vals.len()).to_equal(3)
```

</details>

### Step Generator

#### yields values with custom step size

1. var g =StepGenerator new
2. var vals = collect step
   - Expected: vals.len() equals `4`
   - Expected: vals[0] equals `5`
   - Expected: vals[1] equals `10`
   - Expected: vals[2] equals `15`
   - Expected: vals[3] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var g =StepGenerator.new(0, 5, 20)
var vals = collect_step(g, 100)
expect(vals.len()).to_equal(4)
expect(vals[0]).to_equal(5)
expect(vals[1]).to_equal(10)
expect(vals[2]).to_equal(15)
expect(vals[3]).to_equal(20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)


</details>
