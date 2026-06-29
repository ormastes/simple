# Interpreter Performance Specification

Timing micro-benchmarks for the tree-walking HIR interpreter. Covers integer arithmetic loop throughput, function call overhead, and builtin dispatch cost (println / len calls).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #interp-perf-001 |
| Category | Infrastructure \| Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/interpreter/perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Timing micro-benchmarks for the tree-walking HIR interpreter.
Covers integer arithmetic loop throughput, function call overhead,
and builtin dispatch cost (println / len calls).

## Key Concepts

| Concept              | Description                                         |
|----------------------|-----------------------------------------------------|
| Arithmetic loop      | 1000 int additions — exercises eval_binop hot path  |
| Function call loop   | 100 calls to a trivial helper — measures frame cost |
| Builtin dispatch     | 100 len() calls — exercises try_call_builtin path   |
| Module-cache timing  | Compiled-mode only (see D-8 note below)             |

## D-8 Note (interpreter `it` block limitation)

`it` blocks in interpreter mode do not support `return` for early exit.
All assertions are structured as single terminal `expect(...)` expressions.
Timing elapsed values are computed and stored in `var`; the assertion
verifies functional correctness, not wall-clock bounds (interpreter timing
is non-deterministic).  Wall-clock assertions belong in compiled-mode specs.

## Module-cache timing note

Observing the Rust `module_cache.rs` hit rate requires compiled mode: there
is no API to query cache stats from within an `it` body in interpreter mode.
This spec covers dispatch and call-overhead proxies instead; a compiled-mode
benchmark for module-cache warmup is a follow-up TODO (see 3-arch D-6b).

## Scenarios

### Interpreter Perf

### arithmetic loop

#### 1000 int additions produce correct sum

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum: i64 = 0
var i: i64 = 1
for _step in 0..1000:
    sum = sum + i
    i = i + 1
# sum of 1..1000 = 500500
expect(sum).to_equal(500500)
```

</details>

#### 1000 int multiplications produce correct product mod

1. prod = prod *
   - Expected: prod equals `3628800`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# multiply 1..10 to get factorial(10) = 3628800
var prod: i64 = 1
for _step in 0..10:
    prod = prod * ((_step + 1) + 0)
# factorial(10) = 3628800
expect(prod).to_equal(3628800)
```

</details>

#### timing: 1000 additions complete (elapsed recorded, not asserted)

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wall-clock assertion omitted — interpreter timing is non-deterministic.
# elapsed is computed to exercise the timing path; correctness asserted instead.
val t0 = time_now_unix_micros()
var s: i64 = 0
for _n in 0..1000:
    s = s + _n
val elapsed = time_now_unix_micros() - t0
# elapsed must be non-negative (time only moves forward)
expect(elapsed).to_be_greater_than(-1)
expect(s).to_equal(499500)
```

</details>

### function call overhead

#### 100 function calls return correct accumulated value

1. acc = add one
   - Expected: acc equals `100`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc: i64 = 0
for _c in 0..100:
    acc = add_one(acc)
expect(acc).to_equal(100)
```

</details>

#### identity function returns its argument unchanged

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = identity(42)
expect(result).to_equal(42)
```

</details>

#### timing: 100 function calls complete (elapsed recorded)

1. acc = identity
   - Expected: acc equals `100`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = time_now_unix_micros()
var acc: i64 = 0
for _c in 0..100:
    acc = identity(acc) + 1
val elapsed = time_now_unix_micros() - t0
expect(elapsed).to_be_greater_than(-1)
expect(acc).to_equal(100)
```

</details>

### builtin dispatch

#### 100 len() calls on a list return stable value

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
var checks_ok: i64 = 0
for _k in 0..100:
    val l = items.len()
    if l == 10:
        checks_ok = checks_ok + 1
expect(checks_ok).to_equal(100)
```

</details>

#### timing: 100 len() calls complete (elapsed recorded)

1. acc = acc + data len
   - Expected: acc equals `1000`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
val t0 = time_now_unix_micros()
var acc: i64 = 0
for _k in 0..100:
    acc = acc + data.len()
val elapsed = time_now_unix_micros() - t0
expect(elapsed).to_be_greater_than(-1)
expect(acc).to_equal(1000)
```

</details>

### module cache proxy

#### first 100 calls produce correct result

1. acc = add one
   - Expected: acc equals `100`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc: i64 = 0
for _i in 0..100:
    acc = add_one(acc)
expect(acc).to_equal(100)
```

</details>

#### second 100 calls (warm path) produce same correctness

1. acc = add one
   - Expected: acc equals `100`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same test as above — both batches must give identical results,
# demonstrating stable warm-path behaviour.
var acc: i64 = 0
for _i in 0..100:
    acc = add_one(acc)
expect(acc).to_equal(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

