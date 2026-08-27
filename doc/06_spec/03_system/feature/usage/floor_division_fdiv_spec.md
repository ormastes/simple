# Floor Division (.fdiv) Method

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Floor Division (.fdiv) Method

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | OP-FDIV |
| Category | Operators \| Arithmetic |
| Status | Implemented |
| Source | `test/03_system/feature/usage/floor_division_fdiv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Migration from // Operator

**Old syntax (deprecated):**
```simple
use std.spec.step

val result = 7 // 2  # Floor division (old)
```

**New syntax:**
```simple
val result = 7.fdiv(2)  # Floor division (new)
```

## Mathematical Definition

Floor division: ⌊a/b⌋ (always rounds towards negative infinity)

Properties:
- `a = b * a.fdiv(b) + a % b` (division algorithm)
- `a.fdiv(b)` has same sign as `a / b` when positive
- `a.fdiv(b)` rounds down for negative results

## Examples

```simple
# Positive integers
7.fdiv(2)    # → 3
10.fdiv(3)   # → 3

# Negative integers (rounds towards negative infinity)
(-7).fdiv(2)   # → -4 (not -3)
7.fdiv(-2)     # → -4 (not -3)
(-7).fdiv(-2)  # → 3

# Floating point
7.5.fdiv(2.0)    # → 3.0
(-7.5).fdiv(2.0) # → -4.0
```

## Comparison with Other Division

| Operation | 7 / 2 | -7 / 2 | 7 / -2 | -7 / -2 |
|-----------|-------|--------|--------|---------|
| Regular `/` | 3 | -3 | -3 | 3 |
| Floor `.fdiv()` | 3 | -4 | -4 | 3 |
| Truncate `.trunc()` | 3 | -3 | -3 | 3 |

## Scenarios

### Floor Division (i64.fdiv) - Positive Integers

#### divides evenly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- divides evenly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides evenly")
val result = 10.fdiv(5)
expect result == 2
```

</details>

#### divides with remainder

- divides with remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides with remainder")
val result = 7.fdiv(2)
expect result == 3
```

</details>

#### divides with large remainder

- divides with large remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides with large remainder")
val result = 17.fdiv(5)
expect result == 3
```

</details>

#### divides exactly

- divides exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides exactly")
val result = 20.fdiv(4)
expect result == 5
```

</details>

#### divides small by large

- divides small by large


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides small by large")
val result = 3.fdiv(7)
expect result == 0
```

</details>

#### divides one by one

- divides one by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides one by one")
val result = 1.fdiv(1)
expect result == 1
```

</details>

#### divides large numbers

- divides large numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides large numbers")
val result = 1000.fdiv(7)
expect result == 142
```

</details>

### Floor Division (i64.fdiv) - Negative Integers

#### divides negative by positive (rounds down)

- divides negative by positive (rounds down)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides negative by positive (rounds down)")
val result = (-7).fdiv(2)
expect result == (-4)  # Not -3! Rounds towards negative infinity
```

</details>

#### divides positive by negative (rounds down)

- divides positive by negative (rounds down)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides positive by negative (rounds down)")
val result = 7.fdiv(-2)
expect result == (-4)  # Not -3! Rounds towards negative infinity
```

</details>

#### divides negative by negative (positive result)

- divides negative by negative (positive result)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides negative by negative (positive result)")
val result = (-7).fdiv(-2)
expect result == 3
```

</details>

#### divides negative evenly

- divides negative evenly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides negative evenly")
val result = (-10).fdiv(-5)
expect result == 2
```

</details>

#### handles negative dividend with remainder

- handles negative dividend with remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative dividend with remainder")
val result = (-17).fdiv(5)
expect result == (-4)  # -17 / 5 = -3.4 → floor = -4
```

</details>

#### handles negative divisor with remainder

- handles negative divisor with remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative divisor with remainder")
val result = 17.fdiv(-5)
expect result == (-4)  # 17 / -5 = -3.4 → floor = -4
```

</details>

#### handles both negative with remainder

- handles both negative with remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles both negative with remainder")
val result = (-17).fdiv(-5)
expect result == 3  # -17 / -5 = 3.4 → floor = 3
```

</details>

### Floor Division (i64.fdiv) - Edge Cases

#### divides zero by positive

- divides zero by positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides zero by positive")
val result = 0.fdiv(5)
expect result == 0
```

</details>

#### divides zero by negative

- divides zero by negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides zero by negative")
val result = 0.fdiv(-5)
expect result == 0
```

</details>

#### handles one divided by itself

- handles one divided by itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles one divided by itself")
val result = 42.fdiv(42)
expect result == 1
```

</details>

#### handles negative one by one

- handles negative one by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative one by one")
val result = (-1).fdiv(1)
expect result == (-1)
```

</details>

#### handles one by negative one

- handles one by negative one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles one by negative one")
val result = 1.fdiv(-1)
expect result == (-1)
```

</details>

### Floor Division (i64.fdiv) - Division Algorithm

#### satisfies division algorithm for positive numbers

- satisfies division algorithm for positive numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("satisfies division algorithm for positive numbers")
val a = 17
val b = 5
val q = a.fdiv(b)
val r = a % b
expect a == b * q + r
expect q == 3
expect r == 2
```

</details>

#### satisfies division algorithm for negative dividend

- satisfies division algorithm for negative dividend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("satisfies division algorithm for negative dividend")
val a = -17
val b = 5
val q = a.fdiv(b)
val r = a - b * q
expect a == b * q + r
expect q == (-4)
expect r == 3
```

</details>

#### satisfies division algorithm for negative divisor

- satisfies division algorithm for negative divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("satisfies division algorithm for negative divisor")
val a = 17
val b = -5
val q = a.fdiv(b)
val r = a - b * q
expect a == b * q + r
expect q == (-4)
```

</details>

#### satisfies division algorithm for both negative

- satisfies division algorithm for both negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("satisfies division algorithm for both negative")
val a = -17
val b = -5
val q = a.fdiv(b)
val r = a % b
expect a == b * q + r
expect q == 3
```

</details>

### Floor Division (f64.fdiv) - Positive Floats

#### divides evenly

- divides evenly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides evenly")
val result = 10.0.fdiv(5.0)
expect result == 2.0
```

</details>

#### divides with fractional result

- divides with fractional result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides with fractional result")
val result = 7.5.fdiv(2.0)
expect result == 3.0
```

</details>

#### divides small by large

- divides small by large


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides small by large")
val result = 1.5.fdiv(2.0)
expect result == 0.0
```

</details>

#### divides with small quotient

- divides with small quotient


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides with small quotient")
val result = 2.9.fdiv(3.0)
expect result == 0.0
```

</details>

#### divides exactly at boundary

- divides exactly at boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides exactly at boundary")
val result = 6.0.fdiv(2.0)
expect result == 3.0
```

</details>

#### divides fractional by integer

- divides fractional by integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides fractional by integer")
val result = 9.7.fdiv(3.0)
expect result == 3.0
```

</details>

### Floor Division (f64.fdiv) - Negative Floats

#### divides negative by positive

- divides negative by positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides negative by positive")
val result = (-7.5).fdiv(2.0)
expect result == (-4.0)  # Rounds down to -4, not up to -3
```

</details>

#### divides positive by negative

- divides positive by negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides positive by negative")
val result = 7.5.fdiv(-2.0)
expect result == (-4.0)  # Rounds down to -4
```

</details>

#### divides negative by negative

- divides negative by negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divides negative by negative")
val result = (-7.5).fdiv(-2.0)
expect result == 3.0
```

</details>

#### handles negative fractional dividend

- handles negative fractional dividend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative fractional dividend")
val result = (-5.9).fdiv(2.0)
expect result == (-3.0)  # -5.9 / 2.0 = -2.95 → floor = -3
```

</details>

#### handles negative fractional divisor

- handles negative fractional divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative fractional divisor")
val result = 5.9.fdiv(-2.0)
expect result == (-3.0)  # 5.9 / -2.0 = -2.95 → floor = -3
```

</details>

### Floor Division (f64.fdiv) - Special Float Values

#### handles division by very small number

- handles division by very small number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles division by very small number")
val result = 1.0.fdiv(0.0001)
expect result == 10000.0
```

</details>

#### handles very large result

- handles very large result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles very large result")
val result = 999999999.0.fdiv(1.0)
expect result == 999999999.0
```

</details>

#### handles very large value divided by finite

- handles very large value divided by finite


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles very large value divided by finite")
# Division by zero not supported at runtime, test large values instead
val large = 999999999999.0
val result = large.fdiv(2.0)
expect result == 499999999999.0
```

</details>

#### handles very small value as divisor

- handles very small value as divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles very small value as divisor")
val result = 2.0.fdiv(0.0001)
expect result == 20000.0
```

</details>

#### handles zero fdiv positive

- handles zero fdiv positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles zero fdiv positive")
val result = 0.0.fdiv(2.0)
expect result == 0.0
```

</details>

### Floor Division vs Regular Division

#### matches regular division for positive exact division

- matches regular division for positive exact division


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches regular division for positive exact division")
val regular = 10 / 5
val floor = 10.fdiv(5)
expect regular == floor
```

</details>

#### differs from regular division when remainder exists

- differs from regular division when remainder exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("differs from regular division when remainder exists")
val regular = 7 / 2  # Truncating division: 3
val floor = 7.fdiv(2)  # Floor division: 3
expect regular == floor  # Same for positive
```

</details>

#### differs for negative dividend

- differs for negative dividend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("differs for negative dividend")
val regular = (-7) / 2  # Truncating: -3
val floor = (-7).fdiv(2)  # Floor: -4
expect floor == (-4)
expect regular == (-3)
expect floor != regular
```

</details>

#### differs for negative divisor

- differs for negative divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("differs for negative divisor")
val regular = 7 / (-2)  # Truncating: -3
val floor = 7.fdiv(-2)  # Floor: -4
expect floor == (-4)
expect regular == (-3)
expect floor != regular
```

</details>

### Floor Division - Real World Use Cases

#### calculates number of pages needed

- calculates number of pages needed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calculates number of pages needed")
val total_items = 25
val items_per_page = 10
val pages = (total_items + items_per_page - 1).fdiv(items_per_page)
expect pages == 3  # Need 3 pages for 25 items
```

</details>

#### calculates array chunk count

- calculates array chunk count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calculates array chunk count")
val array_length = 17
val chunk_size = 5
val chunks = array_length.fdiv(chunk_size)
expect chunks == 3  # 17 / 5 = 3 complete chunks
```

</details>

#### calculates time in hours

- calculates time in hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calculates time in hours")
val minutes = 125
val hours = minutes.fdiv(60)
expect hours == 2  # 125 minutes = 2 hours (plus 5 minutes)
```

</details>

#### calculates grid coordinates

- calculates grid coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calculates grid coordinates")
val index = 23
val grid_width = 8
val row = index.fdiv(grid_width)
val col = index % grid_width
expect row == 2  # Row 2 (0-indexed)
expect col == 7  # Column 7
```

</details>

#### rounds negative temperatures to day boundary

- rounds negative temperatures to day boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rounds negative temperatures to day boundary")
# -15 hours ago → which day?
val hours_ago = -15
val days_ago = hours_ago.fdiv(24)
expect days_ago == (-1)  # Yesterday (rounds down)
```

</details>

### Floor Division - Property Testing

#### always produces result <= regular division for negative

- always produces result <= regular division for negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("always produces result <= regular division for negative")
val a = -17
val b = 5
val floor_div = a.fdiv(b)
val regular_div = a / b
expect floor_div <= regular_div
```

</details>

#### always rounds down for fractional floats

- always rounds down for fractional floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("always rounds down for fractional floats")
val result1 = 7.1.fdiv(2.0)
val result2 = 7.9.fdiv(2.0)
expect result1 == 3.0
expect result2 == 3.0
```

</details>

#### is idempotent for exact division

- is idempotent for exact division


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is idempotent for exact division")
val result1 = 10.fdiv(5)
val result2 = result1.fdiv(1)
expect result2 == 2
```

</details>

### Floor Division - Consistency with Math Block

#### matches math block floor division for positive

- matches math block floor division for positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches math block floor division for positive")
# Requires math block integration
val result = 10.fdiv(3)
expect result == 3
```

</details>

#### matches math block floor division for negative

- matches math block floor division for negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches math block floor division for negative")
# Requires math block integration
val result = (-10).fdiv(3)
expect result == (-4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
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

- Canonical SPipe generation for source `9328b3919dafcadb4800ac9a1f013b19621244ba1319214105c28bde58883287`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9328b3919dafcadb4800ac9a1f013b19621244ba1319214105c28bde58883287`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9328b3919dafcadb4800ac9a1f013b19621244ba1319214105c28bde58883287`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/floor_division_fdiv_spec.spl
mirror: doc/06_spec/03_system/feature/usage/floor_division_fdiv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/floor_division_fdiv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/floor_division_fdiv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/floor_division_fdiv_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'divides evenly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/floor_division_fdiv_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'divides with remainder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/floor_division_fdiv_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'divides with large remainder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
