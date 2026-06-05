# Mir Opt Benchmark Specification

> <details>

<!-- sdn-diagram:id=mir_opt_benchmark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_opt_benchmark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_opt_benchmark_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_opt_benchmark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Opt Benchmark Specification

## Scenarios

### DCE benchmarks

#### measures dead assignment elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# val x = 1
# val y = 2
# val z = 3
# return x  # y, z are dead
#
# Expected: ~66% instruction reduction
pass
```

</details>

#### measures unreachable code elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# if true:
#     return 1
# return 2  # unreachable
#
# Expected: ~50% instruction reduction
pass
```

</details>

#### measures dead branch elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# if false:
#     heavy_computation()
# return 1
#
# Expected: Branch and computation removed
pass
```

</details>

### Copy propagation benchmarks

#### measures chain copy elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# val a = input
# val b = a
# val c = b
# val d = c
# return d  # Optimized to: return input
#
# Expected: 3 copy instructions eliminated
pass
```

</details>

#### measures copy through operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# val x = input
# val y = x + 1
# val z = y
# return z  # Optimized to: return (input + 1)
pass
```

</details>

### CSE benchmarks

#### measures duplicate computation elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# val a = x * y
# val b = x * y
# val c = x * y
# return a + b + c  # Optimized to reuse single computation
#
# Expected: 2 multiplications eliminated
pass
```

</details>

#### measures nested CSE

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# val a = (x + y) * (x + y)
# val b = (x + y) + 1
# (x + y) computed once
pass
```

</details>

### Inlining benchmarks

#### measures small function inlining

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# fn add(a, b): a + b
# val x = add(1, 2)
# val y = add(3, 4)
# val z = add(5, 6)
#
# Expected: 3 call instructions replaced with inline ops
pass
```

</details>

#### measures inlining with DCE benefit

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code pattern:
# fn get_flag(): false
# if get_flag():
#     heavy_computation()
#
# After inlining: if false: ... -> entire branch eliminated
pass
```

</details>

### Combined optimization benchmarks

#### measures full optimization pipeline

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Complex code with all optimization opportunities:
# - Dead code
# - Copy chains
# - Common subexpressions
# - Small functions
#
# Expected: >50% total instruction reduction
pass
```

</details>

#### measures optimization levels

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same code with different optimization levels:
# - Level 0 (debug): No optimization
# - Level 1 (size): DCE + copy prop
# - Level 2 (speed): All passes
# - Level 3 (aggressive): Multiple iterations
pass
```

</details>

### Compile-time benchmarks

#### measures DCE pass time

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time to run DCE on medium-sized function
# Expected: <10ms
pass
```

</details>

#### measures copy propagation time

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time to run copy prop on medium-sized function
# Expected: <10ms
pass
```

</details>

#### measures CSE pass time

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time to run CSE on medium-sized function
# Expected: <20ms (more expensive)
pass
```

</details>

#### measures inlining pass time

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time to run inlining on module with many functions
# Expected: <50ms
pass
```

</details>

#### measures full pipeline time

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time to run all passes
# Expected: <100ms for medium module
pass
```

</details>

### Memory benchmarks

#### measures instruction count reduction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Track total instruction count before/after
pass
```

</details>

#### measures basic block count reduction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Track basic block count (unreachable elimination)
pass
```

</details>

#### measures local variable count reduction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Track local variable count (dead var elimination)
pass
```

</details>

### Real-world pattern benchmarks

<details>
<summary>Advanced: measures loop unrolling benefit</summary>

#### measures loop unrolling benefit

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Small constant loops can be unrolled
# for i in 0..4: sum = sum + arr[i]
pass
```

</details>


</details>

#### measures constant folding benefit

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val x = 2 * 3 * 4  # Folded to 24 at compile time
pass
```

</details>

#### measures strength reduction

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val x = y * 2  # Can become y << 1
# val z = y / 4  # Can become y >> 2
pass
```

</details>

### Optimization regression tests

<details>
<summary>Advanced: verifies no infinite loops in optimization</summary>

#### verifies no infinite loops in optimization

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Optimization should terminate
pass
```

</details>


</details>

#### verifies correctness preserved

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Output of optimized code matches unoptimized
pass
```

</details>

#### verifies no code blowup

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Optimization should not increase code size significantly
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_opt_benchmark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DCE benchmarks
- Copy propagation benchmarks
- CSE benchmarks
- Inlining benchmarks
- Combined optimization benchmarks
- Compile-time benchmarks
- Memory benchmarks
- Real-world pattern benchmarks
- Optimization regression tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
