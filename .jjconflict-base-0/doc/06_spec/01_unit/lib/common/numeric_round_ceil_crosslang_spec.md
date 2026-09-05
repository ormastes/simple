# Numeric Round Ceil Crosslang Specification

> Tests covering ceil_f64 — pure-Simple vs C/Rust oracle (rt_math_ceil).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Round Ceil Crosslang Specification

## Scenarios

### ceil_f64 — pure-Simple vs C/Rust oracle (rt_math_ceil)

#### matches the oracle on integer and simple-fraction KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on integer and simple-fraction KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on integer and simple-fraction KATs")
assert_equal(ceil_f64(3.0), 3.0)
assert_equal(ceil_f64(3.0), rt_math_ceil(3.0))
assert_equal(ceil_f64(3.1), 4.0)
assert_equal(ceil_f64(3.1), rt_math_ceil(3.1))
assert_equal(ceil_f64(3.9), 4.0)
assert_equal(ceil_f64(3.9), rt_math_ceil(3.9))
assert_equal(ceil_f64(0.0), 0.0)
assert_equal(ceil_f64(0.0), rt_math_ceil(0.0))
```

</details>

#### matches the oracle on negative-value KATs (ceil rounds toward +infinity)

- matches the oracle on negative-value KATs (ceil rounds toward +infinity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on negative-value KATs (ceil rounds toward +infinity)")
assert_equal(ceil_f64(-3.0), -3.0)
assert_equal(ceil_f64(-3.0), rt_math_ceil(-3.0))
assert_equal(ceil_f64(-3.9), -3.0)
assert_equal(ceil_f64(-3.9), rt_math_ceil(-3.9))
assert_equal(ceil_f64(-0.5), -0.0)
assert_equal(ceil_f64(-0.5), rt_math_ceil(-0.5))
assert_equal(ceil_f64(-0.0001), -0.0)
assert_equal(ceil_f64(-0.0001), rt_math_ceil(-0.0001))
```

</details>

#### matches the oracle on domain-boundary values

- matches the oracle on domain-boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on domain-boundary values")
# +0.0 -> +0.0.
assert_equal(ceil_f64(0.0), 0.0)
assert_equal(ceil_f64(0.0), rt_math_ceil(0.0))

# +infinity -> +infinity, -infinity -> -infinity.
val big = 1.0e308
val pos_inf = big * 10.0
val neg_inf = 0.0 - pos_inf
val pinf_s = ceil_f64(pos_inf)
val pinf_c = rt_math_ceil(pos_inf)
assert_equal(pinf_s, pinf_c)
assert_equal(pinf_s, pos_inf)
val ninf_s = ceil_f64(neg_inf)
val ninf_c = rt_math_ceil(neg_inf)
assert_equal(ninf_s, ninf_c)
assert_equal(ninf_s, neg_inf)

# NaN input -> NaN (checked NaN-safely, since NaN != NaN).
val nan_in = pos_inf - pos_inf
val nan_s = ceil_f64(nan_in)
val nan_c = rt_math_ceil(nan_in)
assert_true(nan_s != nan_s)
assert_true(nan_c != nan_c)

# Large-magnitude integral values beyond i64 range: must be the
# identity, not garbage (the same guard C-MIG-0031 required).
val huge = 1.0e20
assert_equal(ceil_f64(huge), huge)
assert_equal(ceil_f64(huge), rt_math_ceil(huge))
val huge_neg = 0.0 - huge
assert_equal(ceil_f64(huge_neg), huge_neg)
assert_equal(ceil_f64(huge_neg), rt_math_ceil(huge_neg))
```

</details>

#### single-bit input corruption changes the result (discrimination)

- single-bit input corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-bit input corruption changes the result (discrimination)")
assert_true(ceil_f64(3.5) != ceil_f64(4.0000001))
assert_true(rt_math_ceil(3.5) != rt_math_ceil(4.0000001))
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
assert_equal(ceil_f64(7.25), ceil_f64(7.25))
assert_equal(rt_math_ceil(7.25), rt_math_ceil(7.25))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var x = (seed % 1000000) as f64 / 1000.0
    if i % 19 == 0:
        x = 0.0
    else if i % 17 == 0:
        x = -0.0
    else if i % 13 == 0:
        x = 1.0e20
    else if i % 11 == 0:
        x = -1.0e20
    else if i % 7 == 0:
        x = 0.0 - x
    else if i % 5 == 0:
        x = x - 0.5

    val t0 = time_now_unix_micros()
    val s = ceil_f64(x)
    val t1 = time_now_unix_micros()
    val c = rt_math_ceil(x)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_equal(s, c)
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
| Source | `test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ceil_f64 — pure-Simple vs C/Rust oracle (rt_math_ceil).
- ceil_f64 — pure-Simple vs C/Rust oracle (rt_math_ceil)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-CEIL-F64`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02c8be8f3601b3d7a8ae3c61b466ee077f59c5430a59c66b62f1b8892643523c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02c8be8f3601b3d7a8ae3c61b466ee077f59c5430a59c66b62f1b8892643523c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02c8be8f3601b3d7a8ae3c61b466ee077f59c5430a59c66b62f1b8892643523c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/numeric_round_ceil_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/numeric_round_ceil_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/numeric_round_ceil_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on integer and simple-fraction KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on negative-value KATs (ceil rounds toward +infinity)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/numeric_round_ceil_crosslang_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on domain-boundary values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
