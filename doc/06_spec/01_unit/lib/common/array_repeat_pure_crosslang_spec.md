# Array Repeat Pure Crosslang Specification

> Tests covering repeat_int_pure — pure-Simple vs C-backed oracle (rt_array_repeat).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Repeat Pure Crosslang Specification

## Scenarios

### repeat_int_pure — pure-Simple vs C-backed oracle (rt_array_repeat)

#### matches the oracle on ordinary KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary KATs")
assert_equal(repeat_int_pure(7, 3), [7, 7, 7])
assert_equal(repeat_int_pure(7, 3), rt_array_repeat(7, 3))
assert_equal(repeat_int_pure(0, 5), [0, 0, 0, 0, 0])
assert_equal(repeat_int_pure(0, 5), rt_array_repeat(0, 5))
assert_equal(repeat_int_pure(-3, 4), [-3, -3, -3, -3])
assert_equal(repeat_int_pure(-3, 4), rt_array_repeat(-3, 4))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# count = 0: empty result regardless of value.
assert_equal(repeat_int_pure(9, 0), [])
assert_equal(repeat_int_pure(9, 0), rt_array_repeat(9, 0))

# count = 1: single-element result.
assert_equal(repeat_int_pure(42, 1), [42])
assert_equal(repeat_int_pure(42, 1), rt_array_repeat(42, 1))

# Negative count: clamps to empty (same as C's `if (n<0) n=0`).
assert_equal(repeat_int_pure(5, -1), [])
assert_equal(repeat_int_pure(5, -1), rt_array_repeat(5, -1))
assert_equal(repeat_int_pure(5, -1000), [])
assert_equal(repeat_int_pure(5, -1000), rt_array_repeat(5, -1000))

# Value = 0, count = 0: doubly-degenerate boundary.
assert_equal(repeat_int_pure(0, 0), [])
assert_equal(repeat_int_pure(0, 0), rt_array_repeat(0, 0))

# Boundary just past a power-of-two doubling-chunk boundary
# (exercises the C side's doubling-memcpy chunk logic at n=2,
# n=3, n=4, n=5 -- 1->2, 2->4, 4->5 chunk sizes).
assert_equal(repeat_int_pure(1, 2), [1, 1])
assert_equal(repeat_int_pure(1, 2), rt_array_repeat(1, 2))
assert_equal(repeat_int_pure(1, 5), [1, 1, 1, 1, 1])
assert_equal(repeat_int_pure(1, 5), rt_array_repeat(1, 5))

# Large count (oversized-input class).
val big_simple = repeat_int_pure(2, 500)
val big_c = rt_array_repeat(2, 500)
assert_equal(big_simple.len(), 500)
assert_equal(big_simple, big_c)

# Sentinel-adjacent values (0x7f / -0x80 style byte-class edges
# translated to the int domain).
assert_equal(repeat_int_pure(127, 2), rt_array_repeat(127, 2))
assert_equal(repeat_int_pure(-128, 2), rt_array_repeat(-128, 2))
```

</details>

#### single-value change flips the result (discrimination)

- single-value change flips the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-value change flips the result (discrimination)")
assert_true(repeat_int_pure(1, 3) != repeat_int_pure(2, 3))
assert_true(rt_array_repeat(1, 3) != rt_array_repeat(2, 3))
```

</details>

#### is deterministic on both sides

- is deterministic on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic on both sides")
assert_equal(repeat_int_pure(9, 6), repeat_int_pure(9, 6))
assert_equal(rt_array_repeat(9, 6), rt_array_repeat(9, 6))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val values = [0, 1, -1, 7, -7, 100, -100, 127]
val counts = [0, 1, 2, 3, 5, 8, 13, 20]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val value = values[seed % 8]
    val count = counts[(seed / 8) % 8]

    val t0 = time_now_unix_micros()
    val sr = repeat_int_pure(value, count)
    val t1 = time_now_unix_micros()
    val cr = rt_array_repeat(value, count)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_equal(sr, cr)
    i = i + 1
print("perf_evidence: shared_corpus=100 simple_us={simple_us} c_us={c_us}")
assert_true(simple_us >= 0 and c_us >= 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering repeat_int_pure — pure-Simple vs C-backed oracle (rt_array_repeat).
- repeat_int_pure — pure-Simple vs C-backed oracle (rt_array_repeat)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-ARRAY-REPEAT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d8bed105b9fa01c4cee18f44e7cee1f3cb48f8bf0023eef5ea7f43b0c6b3e0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d8bed105b9fa01c4cee18f44e7cee1f3cb48f8bf0023eef5ea7f43b0c6b3e0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d8bed105b9fa01c4cee18f44e7cee1f3cb48f8bf0023eef5ea7f43b0c6b3e0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/array_repeat_pure_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/array_repeat_pure_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/array_repeat_pure_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/array_repeat_pure_crosslang_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-value change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
