# Mir Opt Benchmark Specification

> Tests covering DCE benchmarks, Copy propagation benchmarks, CSE benchmarks, Inlining benchmarks, Combined optimization benchmarks, Compile-time benchmarks, Memory benchmarks, Real-world pattern benchmarks, Optimization regression tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Opt Benchmark Specification

## Scenarios

### DCE benchmarks

#### measures dead assignment elimination

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- measures dead assignment elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures dead assignment elimination")
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

- measures unreachable code elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures unreachable code elimination")
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

- measures dead branch elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures dead branch elimination")
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

- measures chain copy elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures chain copy elimination")
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

- measures copy through operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures copy through operations")
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

- measures duplicate computation elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures duplicate computation elimination")
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

- measures nested CSE


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures nested CSE")
# Code pattern:
# val a = (x + y) * (x + y)
# val b = (x + y) + 1
# (x + y) computed once
pass
```

</details>

### Inlining benchmarks

#### measures small function inlining

- measures small function inlining


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures small function inlining")
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

- measures inlining with DCE benefit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures inlining with DCE benefit")
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

- measures full optimization pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures full optimization pipeline")
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

- measures optimization levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures optimization levels")
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

- measures DCE pass time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures DCE pass time")
# Time to run DCE on medium-sized function
# Expected: <10ms
pass
```

</details>

#### measures copy propagation time

- measures copy propagation time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures copy propagation time")
# Time to run copy prop on medium-sized function
# Expected: <10ms
pass
```

</details>

#### measures CSE pass time

- measures CSE pass time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures CSE pass time")
# Time to run CSE on medium-sized function
# Expected: <20ms (more expensive)
pass
```

</details>

#### measures inlining pass time

- measures inlining pass time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures inlining pass time")
# Time to run inlining on module with many functions
# Expected: <50ms
pass
```

</details>

#### measures full pipeline time

- measures full pipeline time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures full pipeline time")
# Time to run all passes
# Expected: <100ms for medium module
pass
```

</details>

### Memory benchmarks

#### measures instruction count reduction

- measures instruction count reduction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures instruction count reduction")
# Track total instruction count before/after
pass
```

</details>

#### measures basic block count reduction

- measures basic block count reduction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures basic block count reduction")
# Track basic block count (unreachable elimination)
pass
```

</details>

#### measures local variable count reduction

- measures local variable count reduction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures local variable count reduction")
# Track local variable count (dead var elimination)
pass
```

</details>

### Real-world pattern benchmarks

<details>
<summary>Advanced: measures loop unrolling benefit</summary>

#### measures loop unrolling benefit

- measures loop unrolling benefit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures loop unrolling benefit")
# Small constant loops can be unrolled
# for i in 0..4: sum = sum + arr[i]
pass
```

</details>


</details>

#### measures constant folding benefit

- measures constant folding benefit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures constant folding benefit")
# val x = 2 * 3 * 4  # Folded to 24 at compile time
pass
```

</details>

#### measures strength reduction

- measures strength reduction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures strength reduction")
# val x = y * 2  # Can become y << 1
# val z = y / 4  # Can become y >> 2
pass
```

</details>

### Optimization regression tests

<details>
<summary>Advanced: verifies no infinite loops in optimization</summary>

#### verifies no infinite loops in optimization

- verifies no infinite loops in optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies no infinite loops in optimization")
# Optimization should terminate
pass
```

</details>


</details>

#### verifies correctness preserved

- verifies correctness preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies correctness preserved")
# Output of optimized code matches unoptimized
pass
```

</details>

#### verifies no code blowup

- verifies no code blowup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies no code blowup")
# Optimization should not increase code size significantly
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir/mir_opt_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DCE benchmarks, Copy propagation benchmarks, CSE benchmarks, Inlining benchmarks, Combined optimization benchmarks, Compile-time benchmarks, Memory benchmarks, Real-world pattern benchmarks, Optimization regression tests.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88a7b72c5ccfb6583513a81e690c5e9a10d54e52e7b04cc0b8a878eea448e16a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88a7b72c5ccfb6583513a81e690c5e9a10d54e52e7b04cc0b8a878eea448e16a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88a7b72c5ccfb6583513a81e690c5e9a10d54e52e7b04cc0b8a878eea448e16a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/mir/mir_opt_benchmark_spec.spl
mirror: doc/06_spec/unit/compiler/mir/mir_opt_benchmark_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/mir/mir_opt_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir/mir_opt_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir/mir_opt_benchmark_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/mir/mir_opt_benchmark_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures dead assignment elimination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir/mir_opt_benchmark_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures unreachable code elimination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir/mir_opt_benchmark_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures dead branch elimination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
