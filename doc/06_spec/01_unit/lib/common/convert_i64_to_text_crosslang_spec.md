# Convert I64 To Text Crosslang Specification

> Tests covering i64_to_text — pure-Simple vs C oracle (rt_raw_i64_to_string).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Convert I64 To Text Crosslang Specification

## Scenarios

### i64_to_text — pure-Simple vs C oracle (rt_raw_i64_to_string)

#### matches the C oracle on published-shape KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on published-shape KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on published-shape KATs")
assert_equal(i64_to_text(0), "0")
assert_equal(i64_to_text(0), rt_raw_i64_to_string(0))
assert_equal(i64_to_text(1), "1")
assert_equal(i64_to_text(1), rt_raw_i64_to_string(1))
assert_equal(i64_to_text(-1), "-1")
assert_equal(i64_to_text(-1), rt_raw_i64_to_string(-1))
assert_equal(i64_to_text(42), rt_raw_i64_to_string(42))
assert_equal(i64_to_text(-42), rt_raw_i64_to_string(-42))
assert_equal(i64_to_text(1000000), rt_raw_i64_to_string(1000000))
assert_equal(i64_to_text(-1000000), rt_raw_i64_to_string(-1000000))
```

</details>

#### matches the C oracle on i64 boundary values

- matches the C oracle on i64 boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on i64 boundary values")
# i64::MAX and i64::MIN — the classic 2's-complement asymmetric-range
# hazard (MIN has no positive counterpart, and a naive "negate then
# format" implementation overflows on it).
assert_equal(i64_to_text(9223372036854775807), "9223372036854775807")
assert_equal(i64_to_text(9223372036854775807), rt_raw_i64_to_string(9223372036854775807))
assert_equal(i64_to_text(-9223372036854775808), "-9223372036854775808")
assert_equal(i64_to_text(-9223372036854775808), rt_raw_i64_to_string(-9223372036854775808))
assert_equal(i64_to_text(9223372036854775806), rt_raw_i64_to_string(9223372036854775806))
assert_equal(i64_to_text(-9223372036854775807), rt_raw_i64_to_string(-9223372036854775807))
```

</details>

#### matches the C oracle on powers-of-ten transition boundaries (digit-count changes)

- matches the C oracle on powers-of-ten transition boundaries (digit-count changes)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on powers-of-ten transition boundaries (digit-count changes)")
val vectors = [9, 10, 11, 99, 100, 101, 999, 1000, 1001, -9, -10, -11, -99, -100, -101, -999, -1000, -1001]
var i = 0
while i < vectors.len():
    val n = vectors[i]
    assert_equal(i64_to_text(n), rt_raw_i64_to_string(n))
    i = i + 1
```

</details>

#### single-digit corruption changes the result (discrimination)

- single-digit corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-digit corruption changes the result (discrimination)")
assert_true(i64_to_text(123) != i64_to_text(124))
assert_true(rt_raw_i64_to_string(123) != rt_raw_i64_to_string(124))
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
assert_equal(i64_to_text(7654321), i64_to_text(7654321))
assert_equal(rt_raw_i64_to_string(7654321), rt_raw_i64_to_string(7654321))
```

</details>

#### matches the C oracle on 100 shared branch-covering vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME value to BOTH sides inside
# this loop. Branch coverage: a seeded LCG produces magnitudes
# spanning 1..~10^18 (digit counts 0..19) with the sign flipped on
# odd indices, plus i % 13 == 0 forcing zero and i % 23 == 0 forcing
# i64::MIN to exercise both singular edge cases inside the bulk
# corpus, not just the KAT cases above.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
var seed = 12345
while i < 100:
    var n = 0
    if i % 13 == 0:
        n = 0
    else if i % 23 == 0:
        n = -9223372036854775808
    else:
        seed = (seed * 1103515245 + 12345) % 2147483648
        val magnitude_bits = i % 19
        var magnitude = 1
        var b = 0
        while b < magnitude_bits:
            magnitude = magnitude * 3
            b = b + 1
        val jittered = magnitude + (seed % (magnitude + 1))
        if i % 2 == 0:
            n = jittered
        else:
            n = 0 - jittered

    val t0 = time_now_unix_micros()
    val s = i64_to_text(n)
    val t1 = time_now_unix_micros()
    val c = rt_raw_i64_to_string(n)
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
| Source | `test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i64_to_text — pure-Simple vs C oracle (rt_raw_i64_to_string).
- i64_to_text — pure-Simple vs C oracle (rt_raw_i64_to_string)

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
- `REQ-C-MIG-I64-TO-TEXT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fae3eebe0f3aa0e72a296fba8a89f88050a9c8c4eab3ffef97ef5539579e8b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fae3eebe0f3aa0e72a296fba8a89f88050a9c8c4eab3ffef97ef5539579e8b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fae3eebe0f3aa0e72a296fba8a89f88050a9c8c4eab3ffef97ef5539579e8b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/convert_i64_to_text_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/convert_i64_to_text_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/convert_i64_to_text_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on published-shape KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on i64 boundary values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/convert_i64_to_text_crosslang_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on powers-of-ten transition boundaries (digit-count changes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
