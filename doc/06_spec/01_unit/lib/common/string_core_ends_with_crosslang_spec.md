# String Core Ends With Crosslang Specification

> Tests covering str_ends_with — pure-Simple vs C oracle (rt_string_ends_with).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Ends With Crosslang Specification

## Scenarios

### str_ends_with — pure-Simple vs C oracle (rt_string_ends_with)

#### matches the C oracle on published-shape KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on published-shape KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on published-shape KATs")
assert_equal(str_ends_with("", "x"), false)
assert_equal(str_ends_with("", "x"), rt_string_ends_with("", "x"))
assert_equal(str_ends_with("abc", ""), true)
assert_equal(str_ends_with("abc", ""), rt_string_ends_with("abc", ""))
assert_equal(str_ends_with("", ""), true)
assert_equal(str_ends_with("", ""), rt_string_ends_with("", ""))
assert_equal(str_ends_with("abcabc", "abc"), true)
assert_equal(str_ends_with("abcabc", "abc"), rt_string_ends_with("abcabc", "abc"))
assert_equal(str_ends_with("abc", "bc"), true)
assert_equal(str_ends_with("abc", "bc"), rt_string_ends_with("abc", "bc"))
assert_equal(str_ends_with("abc", "z"), false)
assert_equal(str_ends_with("abc", "z"), rt_string_ends_with("abc", "z"))
assert_equal(str_ends_with("abc", "abcd"), false)
assert_equal(str_ends_with("abc", "abcd"), rt_string_ends_with("abc", "abcd"))
assert_equal(str_ends_with("hello.md", ".md"), true)
assert_equal(str_ends_with("hello.md", ".md"), rt_string_ends_with("hello.md", ".md"))
```

</details>

#### matches the C oracle on multibyte UTF-8 suffixes

- matches the C oracle on multibyte UTF-8 suffixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on multibyte UTF-8 suffixes")
# A 2-byte UTF-8 codepoint (e acute, U+00E9) as the suffix and as a
# non-matching corruption. Both sides compare by raw bytes, so a
# partial-codepoint match must not accidentally succeed.
assert_equal(str_ends_with("caf\u{e9}", "\u{e9}"), true)
assert_equal(str_ends_with("caf\u{e9}", "\u{e9}"), rt_string_ends_with("caf\u{e9}", "\u{e9}"))
assert_equal(str_ends_with("caf\u{e9}", "e"), false)
assert_equal(str_ends_with("caf\u{e9}", "e"), rt_string_ends_with("caf\u{e9}", "e"))
```

</details>

#### matches the C oracle on full-match and near-full-match edge cases

- matches the C oracle on full-match and near-full-match edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on full-match and near-full-match edge cases")
val vectors_s = ["aaaa", "aaaa", "mississippi", "hello", "xxxxx", "banana"]
val vectors_n = ["aaaa", "a", "ippi", "hello", "xxxxx", "nana"]
var i = 0
while i < vectors_s.len():
    val s = vectors_s[i]
    val n = vectors_n[i]
    assert_equal(str_ends_with(s, n), rt_string_ends_with(s, n))
    i = i + 1
```

</details>

#### single-char corruption changes the result (discrimination)

- single-char corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char corruption changes the result (discrimination)")
assert_true(str_ends_with("abcabc", "abc") != str_ends_with("abcabc", "abd"))
assert_true(rt_string_ends_with("abcabc", "abc") != rt_string_ends_with("abcabc", "abd"))
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
assert_equal(str_ends_with("determinism", "ism"), str_ends_with("determinism", "ism"))
assert_equal(rt_string_ends_with("determinism", "ism"), rt_string_ends_with("determinism", "ism"))
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
# deterministic generator feeds the SAME subject+suffix pair to BOTH
# sides inside this loop. Branch coverage: subject length 0..99 via a
# seeded LCG over ASCII letters/digits (cycling through a repeated
# 2-char motif "zz" every 6th position to force real-tail-match
# branches), suffix drawn from a short rotating set including an
# empty suffix at i % 11 == 0 and a too-long suffix at i % 17 == 0 to
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
        if j % 6 == 5:
            body = body + "zz"
        else:
            val bucket = seed % 36
            if bucket < 26:
                body = body + ENC_LOWER.char_at(bucket)
            else:
                body = body + ENC_DIGIT.char_at(bucket - 26)
        j = j + 1

    var suffix = "z"
    if i % 11 == 0:
        suffix = ""
    else if i % 17 == 0:
        suffix = body + "yy"
    else if i % 3 == 0:
        suffix = "zz"
    else if i % 3 == 1:
        suffix = ENC_UPPER.char_at(i % 26)
    else:
        suffix = body

    val t0 = time_now_unix_micros()
    val s = str_ends_with(body, suffix)
    val t1 = time_now_unix_micros()
    val c = rt_string_ends_with(body, suffix)
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
| Source | `test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering str_ends_with — pure-Simple vs C oracle (rt_string_ends_with).
- str_ends_with — pure-Simple vs C oracle (rt_string_ends_with)

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
- `REQ-C-MIG-STRING-ENDS-WITH`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3d226df81c3f40fb41a2af02c938a3de3667c2f1de24c8354d0b3ee54235b12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3d226df81c3f40fb41a2af02c938a3de3667c2f1de24c8354d0b3ee54235b12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3d226df81c3f40fb41a2af02c938a3de3667c2f1de24c8354d0b3ee54235b12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_core_ends_with_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/string_core_ends_with_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_core_ends_with_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on published-shape KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on multibyte UTF-8 suffixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_ends_with_crosslang_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on full-match and near-full-match edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
