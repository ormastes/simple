# Numeric Round Is Inf Crosslang Specification

> Tests covering is_inf_f64 — pure-Simple vs C/Rust oracle (rt_math_is_inf).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Round Is Inf Crosslang Specification

## Scenarios

### is_inf_f64 — pure-Simple vs C/Rust oracle (rt_math_is_inf)

#### matches the oracle on ordinary finite KATs (never infinite)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary finite KATs (never infinite)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary finite KATs (never infinite)")
assert_equal(is_inf_f64(0.0), false)
assert_equal(is_inf_f64(0.0), rt_math_is_inf(0.0))
assert_equal(is_inf_f64(-0.0), false)
assert_equal(is_inf_f64(-0.0), rt_math_is_inf(-0.0))
assert_equal(is_inf_f64(3.5), false)
assert_equal(is_inf_f64(3.5), rt_math_is_inf(3.5))
assert_equal(is_inf_f64(-3.5), false)
assert_equal(is_inf_f64(-3.5), rt_math_is_inf(-3.5))
```

</details>

#### matches the oracle on domain-boundary values

- matches the oracle on domain-boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on domain-boundary values")
val big = 1.0e308
val pos_inf = big * 10.0
val neg_inf = 0.0 - pos_inf

# +infinity and -infinity ARE infinite (both signs -- the bug this
# spec found and fixed above was missing the negative side).
assert_equal(is_inf_f64(pos_inf), true)
assert_equal(is_inf_f64(pos_inf), rt_math_is_inf(pos_inf))
assert_equal(is_inf_f64(neg_inf), true)
assert_equal(is_inf_f64(neg_inf), rt_math_is_inf(neg_inf))

# NaN is NOT infinite (checked NaN-safely on the oracle side too).
val nan_in = pos_inf - pos_inf
assert_equal(is_inf_f64(nan_in), false)
assert_equal(is_inf_f64(nan_in), rt_math_is_inf(nan_in))

# Large-magnitude FINITE values beyond i64 range are NOT infinite
# (must not be fooled by magnitude alone -- exactly the false
# positive the rejected doubling-invariant draft produced).
val huge = 1.0e20
assert_equal(is_inf_f64(huge), false)
assert_equal(is_inf_f64(huge), rt_math_is_inf(huge))
val huge_neg = 0.0 - huge
assert_equal(is_inf_f64(huge_neg), false)
assert_equal(is_inf_f64(huge_neg), rt_math_is_inf(huge_neg))

# The largest normal finite f64 is NOT infinite (adjacent-to-the-edge
# boundary case).
assert_equal(is_inf_f64(big), false)
assert_equal(is_inf_f64(big), rt_math_is_inf(big))

# Denormal (subnormal) input is NOT infinite.
val denorm = 5.0e-324
assert_equal(is_inf_f64(denorm), false)
assert_equal(is_inf_f64(denorm), rt_math_is_inf(denorm))
```

</details>

#### single-bit input corruption changes the result (discrimination)

- single-bit input corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-bit input corruption changes the result (discrimination)")
val pos_inf = 1.0e308 * 10.0
assert_true(is_inf_f64(pos_inf) != is_inf_f64(1.0e308))
assert_true(rt_math_is_inf(pos_inf) != rt_math_is_inf(1.0e308))
```

</details>

#### is deterministic on both sides

- is deterministic on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic on both sides")
assert_equal(is_inf_f64(7.25), is_inf_f64(7.25))
assert_equal(rt_math_is_inf(7.25), rt_math_is_inf(7.25))
val pos_inf = 1.0e308 * 10.0
assert_equal(is_inf_f64(pos_inf), is_inf_f64(pos_inf))
assert_equal(rt_math_is_inf(pos_inf), rt_math_is_inf(pos_inf))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val pos_inf = 1.0e308 * 10.0
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var x = (seed % 1000000) as f64 / 1000.0
    if i % 19 == 0:
        x = pos_inf
    else if i % 17 == 0:
        x = 0.0 - pos_inf
    else if i % 13 == 0:
        x = pos_inf - pos_inf          # NaN
    else if i % 11 == 0:
        x = 1.0e308                    # largest finite, adjacent boundary
    else if i % 7 == 0:
        x = 0.0 - x
    else if i % 5 == 0:
        x = -0.0

    val t0 = time_now_unix_micros()
    val s = is_inf_f64(x)
    val t1 = time_now_unix_micros()
    val c = rt_math_is_inf(x)
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
| Source | `test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering is_inf_f64 — pure-Simple vs C/Rust oracle (rt_math_is_inf).
- is_inf_f64 — pure-Simple vs C/Rust oracle (rt_math_is_inf)

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
- `REQ-C-MIG-IS-INF-F64`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87dd6d8d42bac5dc64467559e794bc36e9a150667b32e66faea13899a5faf29c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87dd6d8d42bac5dc64467559e794bc36e9a150667b32e66faea13899a5faf29c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87dd6d8d42bac5dc64467559e794bc36e9a150667b32e66faea13899a5faf29c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary finite KATs (never infinite)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on domain-boundary values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/numeric_round_is_inf_crosslang_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-bit input corruption changes the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
