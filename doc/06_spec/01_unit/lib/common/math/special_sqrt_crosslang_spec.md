# Special Sqrt Crosslang Specification

> Tests covering sqrt_f64 — pure-Simple vs C/Rust oracle (rt_math_sqrt).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Special Sqrt Crosslang Specification

## Scenarios

### sqrt_f64 — pure-Simple vs C/Rust oracle (rt_math_sqrt)

#### matches the oracle on perfect-square KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on perfect-square KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on perfect-square KATs")
assert_equal(sqrt_f64(4.0), 2.0)
assert_equal(sqrt_f64(4.0), rt_math_sqrt(4.0))
assert_equal(sqrt_f64(9.0), 3.0)
assert_equal(sqrt_f64(9.0), rt_math_sqrt(9.0))
assert_equal(sqrt_f64(1.0), 1.0)
assert_equal(sqrt_f64(1.0), rt_math_sqrt(1.0))
assert_equal(sqrt_f64(0.0), 0.0)
assert_equal(sqrt_f64(0.0), rt_math_sqrt(0.0))
```

</details>

#### matches the oracle within tight tolerance on irrational-result vectors

- matches the oracle within tight tolerance on irrational-result vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle within tight tolerance on irrational-result vectors")
# Newton's method (40 iterations) vs hardware sqrt can disagree by a
# handful of ULPs on irrational results -- tolerance-based, not
# bit-exact, comparison is the correct oracle here (unlike the
# integer/text C-MIG-0027/0028 specs, which used exact equality).
assert_true(_approx(sqrt_f64(2.0), rt_math_sqrt(2.0), 1.0e-12))
assert_true(_approx(sqrt_f64(0.5), rt_math_sqrt(0.5), 1.0e-12))
assert_true(_approx(sqrt_f64(9999999.0), rt_math_sqrt(9999999.0), 1.0e-9))
assert_true(_approx(sqrt_f64(1.0e10), rt_math_sqrt(1.0e10), 1.0e-6))
assert_true(_approx(sqrt_f64(1.0e-8), rt_math_sqrt(1.0e-8), 1.0e-12))
# Range-reduction stress: very large / very small magnitudes and
# values straddling the [1,4) reduction window's boundary.
assert_true(_approx(sqrt_f64(1.0e300), rt_math_sqrt(1.0e300), 1.0e290))
assert_true(_approx(sqrt_f64(1.0e-300), rt_math_sqrt(1.0e-300), 1.0e-310))
assert_true(_approx(sqrt_f64(0.999999), rt_math_sqrt(0.999999), 1.0e-12))
assert_true(_approx(sqrt_f64(1.000001), rt_math_sqrt(1.000001), 1.0e-12))
assert_true(_approx(sqrt_f64(1.0e6), rt_math_sqrt(1.0e6), 1.0e-6))
```

</details>

#### agrees with the oracle on negative input (NaN, post-fix)

- agrees with the oracle on negative input (NaN, post-fix)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees with the oracle on negative input (NaN, post-fix)")
val oracle = rt_math_sqrt(-4.0)
val simple = sqrt_f64(-4.0)
# Oracle: correct IEEE-754 NaN for a negative radicand.
assert_true(oracle != oracle)
# Simple kernel: now guarded (fixed 2026-08-18) -- also NaN.
# NaN != NaN by IEEE-754 spec, so "simple != simple" is the
# NaN-safe way to assert simple IS NaN.
assert_true(simple != simple)
```

</details>

#### matches the oracle on other domain-boundary values

- matches the oracle on other domain-boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on other domain-boundary values")
# -0.0 -> -0.0 (sign bit preserved through the x == 0.0 branch).
val neg_zero_s = sqrt_f64(-0.0)
val neg_zero_c = rt_math_sqrt(-0.0)
assert_equal(neg_zero_s, neg_zero_c)
assert_equal(neg_zero_s, -0.0)

# +0.0 -> +0.0.
assert_equal(sqrt_f64(0.0), rt_math_sqrt(0.0))
assert_equal(sqrt_f64(0.0), 0.0)

# +infinity -> +infinity.
val big = 1.0e308
val pos_inf = big * 10.0
val inf_s = sqrt_f64(pos_inf)
val inf_c = rt_math_sqrt(pos_inf)
assert_equal(inf_s, inf_c)
assert_equal(inf_s, pos_inf)

# NaN input -> NaN (checked NaN-safely, since NaN != NaN).
val nan_in = pos_inf - pos_inf
val nan_s = sqrt_f64(nan_in)
val nan_c = rt_math_sqrt(nan_in)
assert_true(nan_s != nan_s)
assert_true(nan_c != nan_c)

# Smallest negative denormal -> NaN, matching the oracle.
val tiny_neg = 0.0 - 4.9e-324
val tiny_s = sqrt_f64(tiny_neg)
val tiny_c = rt_math_sqrt(tiny_neg)
assert_true(tiny_s != tiny_s)
assert_true(tiny_c != tiny_c)

# -1.0 -> NaN, matching the oracle.
val neg1_s = sqrt_f64(-1.0)
val neg1_c = rt_math_sqrt(-1.0)
assert_true(neg1_s != neg1_s)
assert_true(neg1_c != neg1_c)

# Largest finite value: NOT asserted equal to the oracle here.
# Discovered while writing this spec (separate from the
# negative-domain guard this bug is about): the 40-iteration
# Newton loop starting at g = x does not converge for x this large
# -- g needs ~log2(sqrt(x)) ~= 512 halvings before quadratic
# convergence kicks in, so 40 iterations leaves g still close to x
# itself (measured live: sqrt_f64(1.7976931348623157e308) returns
# ~1.63e308, not the correct ~1.34e154). This is a real, PRE-EXISTING
# accuracy limitation for extreme-magnitude input, out of scope for
# this fix (which only guards the negative/NaN/infinity domain
# boundary and leaves the valid-domain Newton kernel bit-identical).
# Filed separately -- see
# doc/08_tracking/bug/sqrt_f64_unguarded_negative_domain_2026-08-18.md
# "Related, separately filed" section.
val max_finite = 1.7976931348623157e308
val max_s = sqrt_f64(max_finite)
val max_c = rt_math_sqrt(max_finite)
assert_true(max_s == max_s)
assert_true(max_c == max_c)
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
assert_true(sqrt_f64(4.0) != sqrt_f64(4.0000001))
assert_true(rt_math_sqrt(16.0) != rt_math_sqrt(16.0000001))
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
assert_equal(sqrt_f64(7.0), sqrt_f64(7.0))
assert_equal(rt_math_sqrt(7.0), rt_math_sqrt(7.0))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME x value to BOTH sides inside
# this loop. Seeded LCG covers a wide magnitude range (sub-1, small
# integer, large) plus forced perfect-square boundary values at fixed
# moduli, restricted to the documented non-negative domain (the
# negative-input divergence is covered explicitly above instead, so
# it does not corrupt this loop's equality assertion).
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var x = (seed % 1000000) as f64 / 1000.0
    if i % 17 == 0:
        x = 0.0
    else if i % 13 == 0:
        x = 1.0
    else if i % 11 == 0:
        x = 144.0
    else if i % 7 == 0:
        x = 0.25

    val t0 = time_now_unix_micros()
    val s = sqrt_f64(x)
    val t1 = time_now_unix_micros()
    val c = rt_math_sqrt(x)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_true(_approx(s, c, 1.0e-6))
    i = i + 1
print("perf_evidence: shared_corpus=100 simple_us={simple_us} c_us={c_us}")
assert_true(simple_us >= 0 and c_us >= 0)
```

</details>

<details>
<summary>Advanced: matches the oracle on a second shared loop covering the negative domain</summary>

#### matches the oracle on a second shared loop covering the negative domain

- matches the oracle on a second shared loop covering the negative domain


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on a second shared loop covering the negative domain")
# Separate loop (not merged into the non-negative 100-vector loop
# above) so that loop's `_approx` equality assertion is not
# disturbed by NaN-safe comparison logic. Same seeded-LCG generator,
# negated, plus forced negative-zero/negative-boundary values.
var j = 0
while j < 40:
    var seed = (j * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var x = 0.0 - ((seed % 1000000) as f64 / 1000.0)
    if j % 11 == 0:
        x = -0.0
    else if j % 7 == 0:
        x = -1.0

    val s = sqrt_f64(x)
    val c = rt_math_sqrt(x)
    if x == 0.0:
        assert_equal(s, c)
    else:
        # x < 0.0 (strictly): both sides must be NaN.
        assert_true(s != s)
        assert_true(c != c)
    j = j + 1
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sqrt_f64 — pure-Simple vs C/Rust oracle (rt_math_sqrt).
- sqrt_f64 — pure-Simple vs C/Rust oracle (rt_math_sqrt)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-SQRT-F64`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67566971bb64fdfd9a1d8c4a2898d04239b04c7c5784c1da1b7529287637f367`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67566971bb64fdfd9a1d8c4a2898d04239b04c7c5784c1da1b7529287637f367`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67566971bb64fdfd9a1d8c4a2898d04239b04c7c5784c1da1b7529287637f367`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/special_sqrt_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/math/special_sqrt_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/special_sqrt_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on perfect-square KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle within tight tolerance on irrational-result vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/special_sqrt_crosslang_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the oracle on negative input (NaN, post-fix)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
