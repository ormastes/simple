# Suffix Pure Ext Crosslang Specification

> Tests covering ends_with_text — pure-Simple vs C-backed oracle (rt_string_ends_with).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Suffix Pure Ext Crosslang Specification

## Scenarios

### ends_with_text — pure-Simple vs C-backed oracle (rt_string_ends_with)

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
assert_equal(ends_with_text("hello.txt", ".txt"), true)
assert_equal(ends_with_text("hello.txt", ".txt"), rt_string_ends_with("hello.txt", ".txt"))
assert_equal(ends_with_text("hello.txt", ".md"), false)
assert_equal(ends_with_text("hello.txt", ".md"), rt_string_ends_with("hello.txt", ".md"))
assert_equal(ends_with_text("archive.tar.gz", "tar.gz"), true)
assert_equal(ends_with_text("archive.tar.gz", "tar.gz"), rt_string_ends_with("archive.tar.gz", "tar.gz"))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# Empty subject, empty suffix.
assert_equal(ends_with_text("", ""), true)
assert_equal(ends_with_text("", ""), rt_string_ends_with("", ""))

# Empty suffix against non-empty subject: always matches.
assert_equal(ends_with_text("abc", ""), true)
assert_equal(ends_with_text("abc", ""), rt_string_ends_with("abc", ""))

# Empty subject, non-empty suffix: never matches.
assert_equal(ends_with_text("", "abc"), false)
assert_equal(ends_with_text("", "abc"), rt_string_ends_with("", "abc"))

# Suffix longer than subject.
assert_equal(ends_with_text("ab", "abcdef"), false)
assert_equal(ends_with_text("ab", "abcdef"), rt_string_ends_with("ab", "abcdef"))

# Suffix exactly equal to subject.
assert_equal(ends_with_text("abc", "abc"), true)
assert_equal(ends_with_text("abc", "abc"), rt_string_ends_with("abc", "abc"))

# Single-char subject, single-char suffix, match and mismatch.
assert_equal(ends_with_text("a", "a"), true)
assert_equal(ends_with_text("a", "a"), rt_string_ends_with("a", "a"))
assert_equal(ends_with_text("a", "b"), false)
assert_equal(ends_with_text("a", "b"), rt_string_ends_with("a", "b"))

# Suffix matches a substring in the middle but not the tail.
assert_equal(ends_with_text("abcabc", "abc"), true)
assert_equal(ends_with_text("abcabc", "abc"), rt_string_ends_with("abcabc", "abc"))
assert_equal(ends_with_text("abcabd", "abc"), false)
assert_equal(ends_with_text("abcabd", "abc"), rt_string_ends_with("abcabd", "abc"))

# Multibyte UTF-8 suffix, matching and not matching.
assert_equal(ends_with_text("caf\u{e9}", "\u{e9}"), true)
assert_equal(ends_with_text("caf\u{e9}", "\u{e9}"), rt_string_ends_with("caf\u{e9}", "\u{e9}"))
assert_equal(ends_with_text("hello", "\u{e9}"), false)
assert_equal(ends_with_text("hello", "\u{e9}"), rt_string_ends_with("hello", "\u{e9}"))

# All-whitespace subject and suffix.
assert_equal(ends_with_text("   ", " "), true)
assert_equal(ends_with_text("   ", " "), rt_string_ends_with("   ", " "))

# Byte-class boundary: NUL (0x00) and DEL (0x7f) chars in subject.
assert_equal(ends_with_text("x\u{0}", "\u{0}"), true)
assert_equal(ends_with_text("x\u{0}", "\u{0}"), rt_string_ends_with("x\u{0}", "\u{0}"))
assert_equal(ends_with_text("x\u{7f}", "\u{7f}"), true)
assert_equal(ends_with_text("x\u{7f}", "\u{7f}"), rt_string_ends_with("x\u{7f}", "\u{7f}"))
```

</details>

#### single-char input change flips the result (discrimination)

- single-char input change flips the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char input change flips the result (discrimination)")
assert_true(ends_with_text("hello.txt", ".txt") != ends_with_text("hello.tst", ".txt"))
assert_true(rt_string_ends_with("hello.txt", ".txt") != rt_string_ends_with("hello.tst", ".txt"))
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
assert_equal(ends_with_text("a/b/c.spl", ".spl"), ends_with_text("a/b/c.spl", ".spl"))
assert_equal(rt_string_ends_with("a/b/c.spl", ".spl"), rt_string_ends_with("a/b/c.spl", ".spl"))
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
val subjects = ["hello.txt", "archive.tar.gz", "readme", "", "a", "日本語.txt", "abcabc", "x"]
val suffixes = [".txt", "gz", "", "hello", "z", "\u{6587}", "abc", "xyz"]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val subj = subjects[seed % 8]
    val suf = suffixes[(seed / 8) % 8]

    val t0 = time_now_unix_micros()
    val sr = ends_with_text(subj, suf)
    val t1 = time_now_unix_micros()
    val cr = rt_string_ends_with(subj, suf)
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
| Source | `test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ends_with_text — pure-Simple vs C-backed oracle (rt_string_ends_with).
- ends_with_text — pure-Simple vs C-backed oracle (rt_string_ends_with)

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
- `REQ-C-MIG-SUFFIX-ENDS-WITH`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f768f109bd069ebf64c0273e43b22fec61708d1524ce2658716c99fcb26c60b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f768f109bd069ebf64c0273e43b22fec61708d1524ce2658716c99fcb26c60b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f768f109bd069ebf64c0273e43b22fec61708d1524ce2658716c99fcb26c60b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/suffix_pure_ext_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/suffix_pure_ext_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/suffix_pure_ext_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/suffix_pure_ext_crosslang_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char input change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
