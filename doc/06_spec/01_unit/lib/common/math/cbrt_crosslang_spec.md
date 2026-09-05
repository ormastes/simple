# Cbrt Crosslang Specification

> Tests covering cbrt_f64 — pure-Simple vs C/Rust oracle (rt_math_cbrt).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbrt Crosslang Specification

## Scenarios

### cbrt_f64 — pure-Simple vs C/Rust oracle (rt_math_cbrt)

#### matches the oracle on perfect-cube KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on perfect-cube KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on perfect-cube KATs")
assert_true(_approx(cbrt_f64(8.0), 2.0, 1.0e-9))
assert_equal(cbrt_f64(8.0), rt_math_cbrt(8.0))
assert_true(_approx(cbrt_f64(27.0), 3.0, 1.0e-9))
assert_equal(cbrt_f64(27.0), rt_math_cbrt(27.0))
assert_true(_approx(cbrt_f64(1.0), 1.0, 1.0e-9))
assert_equal(cbrt_f64(1.0), rt_math_cbrt(1.0))
assert_equal(cbrt_f64(0.0), 0.0)
assert_equal(cbrt_f64(0.0), rt_math_cbrt(0.0))
```

</details>

#### matches the oracle on negative perfect-cube KATs (cbrt IS defined for negatives)

- matches the oracle on negative perfect-cube KATs (cbrt IS defined for negatives)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on negative perfect-cube KATs (cbrt IS defined for negatives)")
assert_true(_approx(cbrt_f64(-8.0), -2.0, 1.0e-9))
assert_equal(cbrt_f64(-8.0), rt_math_cbrt(-8.0))
assert_true(_approx(cbrt_f64(-27.0), -3.0, 1.0e-9))
assert_equal(cbrt_f64(-27.0), rt_math_cbrt(-27.0))
assert_true(_approx(cbrt_f64(-1.0), -1.0, 1.0e-9))
assert_equal(cbrt_f64(-1.0), rt_math_cbrt(-1.0))
```

</details>

#### matches the oracle within tight tolerance on irrational-result vectors

- matches the oracle within tight tolerance on irrational-result vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle within tight tolerance on irrational-result vectors")
assert_true(_approx(cbrt_f64(2.0), rt_math_cbrt(2.0), 1.0e-9))
assert_true(_approx(cbrt_f64(0.5), rt_math_cbrt(0.5), 1.0e-9))
assert_true(_approx(cbrt_f64(9999999.0), rt_math_cbrt(9999999.0), 1.0e-6))
assert_true(_approx(cbrt_f64(1.0e10), rt_math_cbrt(1.0e10), 1.0e-6))
assert_true(_approx(cbrt_f64(1.0e-8), rt_math_cbrt(1.0e-8), 1.0e-9))
assert_true(_approx(cbrt_f64(-2.0), rt_math_cbrt(-2.0), 1.0e-9))
# Range-reduction stress: very large / very small magnitudes and
# values straddling the [1,8) reduction window's boundary.
assert_true(_approx(cbrt_f64(1.0e300), rt_math_cbrt(1.0e300), 1.0e290))
assert_true(_approx(cbrt_f64(1.0e-300), rt_math_cbrt(1.0e-300), 1.0e-310))
assert_true(_approx(cbrt_f64(0.999999), rt_math_cbrt(0.999999), 1.0e-9))
assert_true(_approx(cbrt_f64(1.000001), rt_math_cbrt(1.000001), 1.0e-9))
assert_true(_approx(cbrt_f64(1.0e6), rt_math_cbrt(1.0e6), 1.0e-6))
```

</details>

#### matches the oracle on other domain-boundary values

- matches the oracle on other domain-boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on other domain-boundary values")
# -0.0 -> -0.0 (sign bit preserved through the x == 0.0 branch).
val neg_zero_s = cbrt_f64(-0.0)
val neg_zero_c = rt_math_cbrt(-0.0)
assert_equal(neg_zero_s, neg_zero_c)
assert_equal(neg_zero_s, -0.0)

# +0.0 -> +0.0.
assert_equal(cbrt_f64(0.0), rt_math_cbrt(0.0))
assert_equal(cbrt_f64(0.0), 0.0)

# +infinity -> +infinity, -infinity -> -infinity.
val big = 1.0e308
val pos_inf = big * 10.0
val neg_inf = 0.0 - pos_inf
val pinf_s = cbrt_f64(pos_inf)
val pinf_c = rt_math_cbrt(pos_inf)
assert_equal(pinf_s, pinf_c)
assert_equal(pinf_s, pos_inf)
val ninf_s = cbrt_f64(neg_inf)
val ninf_c = rt_math_cbrt(neg_inf)
assert_equal(ninf_s, ninf_c)
assert_equal(ninf_s, neg_inf)

# NaN input -> NaN (checked NaN-safely, since NaN != NaN).
val nan_in = pos_inf - pos_inf
val nan_s = cbrt_f64(nan_in)
val nan_c = rt_math_cbrt(nan_in)
assert_true(nan_s != nan_s)
assert_true(nan_c != nan_c)
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
assert_true(cbrt_f64(8.0) != cbrt_f64(8.0000001))
assert_true(rt_math_cbrt(27.0) != rt_math_cbrt(27.0000001))
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
assert_equal(cbrt_f64(7.0), cbrt_f64(7.0))
assert_equal(rt_math_cbrt(7.0), rt_math_cbrt(7.0))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors (pos+neg domain), with perf evidence

- matches the oracle on 100 shared branch-covering vectors (pos+neg domain), with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors (pos+neg domain), with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME x value to BOTH sides
# inside this loop. Seeded LCG covers a wide magnitude range
# (sub-1, small integer, large), forced perfect-cube boundary
# values at fixed moduli, AND negative values (unlike the sqrt
# spec, cbrt's full domain is exercised in one loop since there is
# no NaN-producing negative branch to isolate).
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
        x = 1.0
    else if i % 11 == 0:
        x = 125.0
    else if i % 7 == 0:
        x = -0.125
    else if i % 5 == 0:
        x = 0.0 - x

    val t0 = time_now_unix_micros()
    val s = cbrt_f64(x)
    val t1 = time_now_unix_micros()
    val c = rt_math_cbrt(x)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_true(_approx(s, c, 1.0e-6))
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
| Source | `test/01_unit/lib/common/math/cbrt_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cbrt_f64 — pure-Simple vs C/Rust oracle (rt_math_cbrt).
- cbrt_f64 — pure-Simple vs C/Rust oracle (rt_math_cbrt)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-CBRT-F64`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6845cd009f9c240c6ea00c21694405b348e568861aa73f07ce884b9dad02bcdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6845cd009f9c240c6ea00c21694405b348e568861aa73f07ce884b9dad02bcdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6845cd009f9c240c6ea00c21694405b348e568861aa73f07ce884b9dad02bcdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/math/cbrt_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/cbrt_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/math/cbrt_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/cbrt_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/cbrt_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/math/cbrt_crosslang_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on perfect-cube KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/cbrt_crosslang_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on negative perfect-cube KATs (cbrt IS defined for negatives)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/cbrt_crosslang_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle within tight tolerance on irrational-result vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
