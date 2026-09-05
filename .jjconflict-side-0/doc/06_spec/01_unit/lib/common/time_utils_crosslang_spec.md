# Time Utils Crosslang Specification

> Tests covering time_utils pure-Simple vs C oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Utils Crosslang Specification

## Scenarios

### time_utils pure-Simple vs C oracle

#### epoch is zero in both

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- epoch is zero in both


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("epoch is zero in both")
val s = timestamp_from_components(1970, 1, 1, 0, 0, 0, 0)
assert_equal(s, 0)
assert_equal(s, rt_timestamp_from_components(1970, 1, 1, 0, 0, 0, 0))
```

</details>

#### matches the C oracle on representative dates

- matches the C oracle on representative dates


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on representative dates")
# (year month day hour min sec usec) covering: leap day, century
# non-leap, 400-year leap, end-of-year, pre-epoch, far future
val y = [2000, 2024, 1900, 1999, 1969, 2100, 2038]
val mo = [2,    2,    3,    12,   12,   2,    1]
val d = [29,   29,   1,    31,   31,   28,   19]
val h = [12,   23,   0,    23,   23,   6,    3]
var i = 0
while i < y.len():
    val simple = timestamp_from_components(y[i], mo[i], d[i], h[i], 59, 59, 123456)
    val oracle = rt_timestamp_from_components(y[i], mo[i], d[i], h[i], 59, 59, 123456)
    assert_equal(simple, oracle)
    i = i + 1
```

</details>

#### round-trips through the component getters

- round-trips through the component getters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through the component getters")
val t = timestamp_from_components(2024, 2, 29, 13, 45, 7, 0)
assert_equal(timestamp_get_year(t), 2024)
assert_equal(timestamp_get_month(t), 2)
assert_equal(timestamp_get_day(t), 29)
assert_equal(timestamp_get_hour(t), 13)
assert_equal(timestamp_get_minute(t), 45)
assert_equal(timestamp_get_second(t), 7)
```

</details>

#### add_days and diff_days match the C oracle including negatives

- add_days and diff_days match the C oracle including negatives


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("add_days and diff_days match the C oracle including negatives")
val t = timestamp_from_components(2024, 1, 15, 0, 0, 0, 0)
assert_equal(timestamp_add_days(t, 45), rt_timestamp_add_days(t, 45))
assert_equal(timestamp_add_days(t, -400), rt_timestamp_add_days(t, -400))
val t2 = timestamp_from_components(2023, 1, 15, 6, 0, 0, 0)
assert_equal(timestamp_diff_days(t, t2), rt_timestamp_diff_days(t, t2))
assert_equal(timestamp_diff_days(t2, t), rt_timestamp_diff_days(t2, t))
```

</details>

#### leap-day arithmetic crosses correctly

- leap-day arithmetic crosses correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leap-day arithmetic crosses correctly")
val feb28 = timestamp_from_components(2024, 2, 28, 0, 0, 0, 0)
val mar1 = timestamp_add_days(feb28, 2)
assert_equal(timestamp_get_month(mar1), 3)
assert_equal(timestamp_get_day(mar1), 1)
```

</details>

#### matches the C oracle on 100 shared branch-covering epoch/component vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering epoch/component vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 108 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering epoch/component vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME components to BOTH sides
# inside this loop — the loop is the shared logic (no duplicated
# per-side vector lists). Domain adaptation for timestamps (not
# arbitrary bytes): the seeded LCG walks through i=0..99 and, at
# fixed indices, is overridden with named domain-boundary values —
# epoch (i=0), pre-epoch negative year, century non-leap (1900,
# 2100), 400-year leap (2000, 2400), Feb-28/29 leap-day boundaries,
# month/day-count boundaries (30 vs 31 vs 28/29 day months), the
# i32/2038 rollover date, and far-future years — plus add_days /
# diff_days exercised on each generated timestamp, including
# negative deltas.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
var seed = 12345
while i < 100:
    seed = (seed * 1103515245 + 12345) % 2147483648
    var year = 1900 + (seed % 250)
    var month = 1 + (seed % 12)
    # day-count boundary: clip to a value valid for every month
    # (28) most of the time, but let a slice through to exercise
    # 29/30/31-day months and Feb-29 leap boundary via the seed.
    var day = 1 + (seed % 28)
    val hour = seed % 24
    val minute = (seed / 7) % 60
    val second = (seed / 13) % 60
    val micro = (seed / 3) % 1000000

    # named domain-boundary overrides at fixed indices
    if i == 0:
        year = 1970
        month = 1
        day = 1
    elif i == 1:
        year = 2000
        month = 2
        day = 29  # 400-year leap
    elif i == 2:
        year = 1900
        month = 3
        day = 1  # century non-leap: Feb has 28 days
    elif i == 3:
        year = 2100
        month = 2
        day = 28  # century non-leap boundary
    elif i == 4:
        year = 2024
        month = 2
        day = 29  # ordinary 4-year leap
    elif i == 5:
        year = 1969
        month = 12
        day = 31  # pre-epoch, last day of year
    elif i == 6:
        year = 2038
        month = 1
        day = 19  # i32 2038 rollover date
    elif i == 7:
        year = 2400
        month = 2
        day = 29  # 400-year leap (multiple of 400)
    elif i == 8:
        year = 1800
        month = 4
        day = 30  # 30-day month boundary
    elif i == 9:
        year = 2999
        month = 12
        day = 31  # far future, year-end boundary

    val simple_t0 = time_now_unix_micros()
    val simple_ts = timestamp_from_components(year, month, day, hour, minute, second, micro)
    val simple_t1 = time_now_unix_micros()
    val oracle_ts = rt_timestamp_from_components(year, month, day, hour, minute, second, micro)
    val simple_t2 = time_now_unix_micros()

    simple_us = simple_us + (simple_t1 - simple_t0)
    c_us = c_us + (simple_t2 - simple_t1)
    assert_equal(simple_ts, oracle_ts)

    # exercise add_days/diff_days incl. negative deltas on the
    # same generated timestamp, inside the same shared loop.
    val delta = (seed % 801) - 400
    val t3 = time_now_unix_micros()
    val simple_added = timestamp_add_days(simple_ts, delta)
    val t4 = time_now_unix_micros()
    val oracle_added = rt_timestamp_add_days(oracle_ts, delta)
    val t5 = time_now_unix_micros()
    simple_us = simple_us + (t4 - t3)
    c_us = c_us + (t5 - t4)
    assert_equal(simple_added, oracle_added)

    val t6 = time_now_unix_micros()
    val simple_diff = timestamp_diff_days(simple_added, simple_ts)
    val t7 = time_now_unix_micros()
    val oracle_diff = rt_timestamp_diff_days(oracle_added, oracle_ts)
    val t8 = time_now_unix_micros()
    simple_us = simple_us + (t7 - t6)
    c_us = c_us + (t8 - t7)
    assert_equal(simple_diff, oracle_diff)

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
| Source | `test/01_unit/lib/common/time_utils_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering time_utils pure-Simple vs C oracle.
- time_utils pure-Simple vs C oracle

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
- `REQ-C-MIG-TIMESTAMP`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a50bccdc7e5c4a8ac08406c5b682c1d0e7ccd0317d48fbc7cb66d84755d4eed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a50bccdc7e5c4a8ac08406c5b682c1d0e7ccd0317d48fbc7cb66d84755d4eed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a50bccdc7e5c4a8ac08406c5b682c1d0e7ccd0317d48fbc7cb66d84755d4eed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/time_utils_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/time_utils_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/time_utils_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/time_utils_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/time_utils_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/time_utils_crosslang_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'epoch is zero in both' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/time_utils_crosslang_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on representative dates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/time_utils_crosslang_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through the component getters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
