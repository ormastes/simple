# String Core Rfind Crosslang Specification

> Tests covering str_last_index_of — pure-Simple vs C oracle (rt_string_rfind).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Rfind Crosslang Specification

## Scenarios

### str_last_index_of — pure-Simple vs C oracle (rt_string_rfind)

#### matches the C oracle on published-shape KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on published-shape KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on published-shape KATs")
assert_equal(str_last_index_of("", "x"), -1)
assert_equal(str_last_index_of("", "x"), rt_string_rfind("", "x"))
assert_equal(str_last_index_of("abc", ""), 3)
assert_equal(str_last_index_of("abc", ""), rt_string_rfind("abc", ""))
assert_equal(str_last_index_of("abcabc", "a"), 3)
assert_equal(str_last_index_of("abcabc", "a"), rt_string_rfind("abcabc", "a"))
assert_equal(str_last_index_of("abcabc", "bc"), 4)
assert_equal(str_last_index_of("abcabc", "bc"), rt_string_rfind("abcabc", "bc"))
assert_equal(str_last_index_of("abc", "z"), -1)
assert_equal(str_last_index_of("abc", "z"), rt_string_rfind("abc", "z"))
assert_equal(str_last_index_of("abc", "abcd"), -1)
assert_equal(str_last_index_of("abc", "abcd"), rt_string_rfind("abc", "abcd"))
```

</details>

#### matches the C oracle on overlapping-needle and full-match edge cases

- matches the C oracle on overlapping-needle and full-match edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on overlapping-needle and full-match edge cases")
val vectors_s = ["aaaa", "aaaa", "mississippi", "hello", "xxxxx", "banana"]
val vectors_n = ["aa", "a", "iss", "hello", "xxxxx", "ana"]
var i = 0
while i < vectors_s.len():
    val s = vectors_s[i]
    val n = vectors_n[i]
    assert_equal(str_last_index_of(s, n), rt_string_rfind(s, n))
    i = i + 1
```

</details>

#### single-char corruption changes the found offset (discrimination)

- single-char corruption changes the found offset (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char corruption changes the found offset (discrimination)")
assert_true(str_last_index_of("abcabc", "b") != str_last_index_of("abcabc", "c"))
assert_true(rt_string_rfind("abcabc", "b") != rt_string_rfind("abcabc", "c"))
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
assert_equal(str_last_index_of("determinism", "min"), str_last_index_of("determinism", "min"))
assert_equal(rt_string_rfind("determinism", "min"), rt_string_rfind("determinism", "min"))
```

</details>

#### matches the C oracle on 100 shared branch-covering vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME subject+needle pair to BOTH
# sides inside this loop. Branch coverage: subject length 0..99 via a
# seeded LCG over ASCII letters/digits (cycling through a repeated
# 2-char motif "ab" every 5th position to force overlapping-match
# branches), needle drawn from a short rotating set including an
# empty needle at i % 11 == 0 and a too-long needle at i % 17 == 0 to
# exercise both boundary return paths.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var body = ""
    var seed = i * 2654435761 % 4294967296
    val len = i
    var j = 0
    while j < len:
        seed = (seed * 1103515245 + 12345) % 2147483648
        if j % 5 == 4:
            body = body + "ab"
        else:
            val bucket = seed % 36
            if bucket < 26:
                body = body + ENC_LOWER.char_at(bucket)
            else:
                body = body + ENC_DIGIT.char_at(bucket - 26)
        j = j + 1

    var needle = "a"
    if i % 11 == 0:
        needle = ""
    else if i % 17 == 0:
        needle = body + "zz"
    else if i % 3 == 0:
        needle = "ab"
    else if i % 3 == 1:
        needle = ENC_UPPER.char_at(i % 26)
    else:
        needle = body

    val t0 = time_now_unix_micros()
    val s = str_last_index_of(body, needle)
    val t1 = time_now_unix_micros()
    val c = rt_string_rfind(body, needle)
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
| Source | `test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering str_last_index_of — pure-Simple vs C oracle (rt_string_rfind).
- str_last_index_of — pure-Simple vs C oracle (rt_string_rfind)

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
- `REQ-C-MIG-STRING-RFIND`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf723a887d4e8f0461586b6f2b48d7bfce736ea5dcd8b39f8b7882569e547cf7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf723a887d4e8f0461586b6f2b48d7bfce736ea5dcd8b39f8b7882569e547cf7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf723a887d4e8f0461586b6f2b48d7bfce736ea5dcd8b39f8b7882569e547cf7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_core_rfind_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/string_core_rfind_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_core_rfind_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on published-shape KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on overlapping-needle and full-match edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_rfind_crosslang_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char corruption changes the found offset (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
