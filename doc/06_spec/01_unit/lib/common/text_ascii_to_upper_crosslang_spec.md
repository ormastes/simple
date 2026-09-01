# Text Ascii To Upper Crosslang Specification

> Tests covering to_upper_ascii — pure-Simple vs Rust-interpreter oracle (rt_text_to_upper_ascii).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Ascii To Upper Crosslang Specification

## Scenarios

### to_upper_ascii — pure-Simple vs Rust-interpreter oracle (rt_text_to_upper_ascii)

#### matches the oracle on ordinary KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary KATs")
assert_equal(to_upper_ascii("hello"), "HELLO")
assert_equal(to_upper_ascii("hello"), rt_text_to_upper_ascii("hello"))
assert_equal(to_upper_ascii("Hello World"), "HELLO WORLD")
assert_equal(to_upper_ascii("Hello World"), rt_text_to_upper_ascii("Hello World"))
assert_equal(to_upper_ascii("ALREADY UPPER"), "ALREADY UPPER")
assert_equal(to_upper_ascii("ALREADY UPPER"), rt_text_to_upper_ascii("ALREADY UPPER"))
assert_equal(to_upper_ascii("MiXeD123"), "MIXED123")
assert_equal(to_upper_ascii("MiXeD123"), rt_text_to_upper_ascii("MiXeD123"))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# Empty string.
assert_equal(to_upper_ascii(""), "")
assert_equal(to_upper_ascii(""), rt_text_to_upper_ascii(""))

# Single char, lower and upper.
assert_equal(to_upper_ascii("a"), "A")
assert_equal(to_upper_ascii("a"), rt_text_to_upper_ascii("a"))
assert_equal(to_upper_ascii("Z"), "Z")
assert_equal(to_upper_ascii("Z"), rt_text_to_upper_ascii("Z"))

# All-whitespace: no letters to touch.
assert_equal(to_upper_ascii("   "), "   ")
assert_equal(to_upper_ascii("   "), rt_text_to_upper_ascii("   "))

# Digits and punctuation: byte-wise passthrough, not letters.
assert_equal(to_upper_ascii("123-456_789!"), "123-456_789!")
assert_equal(to_upper_ascii("123-456_789!"), rt_text_to_upper_ascii("123-456_789!"))

# Non-ASCII multibyte UTF-8: must pass through unchanged (byte-wise
# ASCII-only semantics, not a Unicode-aware case fold).
assert_equal(to_upper_ascii("café"), "CAFé")
assert_equal(to_upper_ascii("café"), rt_text_to_upper_ascii("café"))
assert_equal(to_upper_ascii("日本語"), "日本語")
assert_equal(to_upper_ascii("日本語"), rt_text_to_upper_ascii("日本語"))

# Multibyte character directly adjacent to an ASCII lowercase run
# at the boundary.
assert_equal(to_upper_ascii("aé b"), "Aé B")
assert_equal(to_upper_ascii("aé b"), rt_text_to_upper_ascii("aé b"))
```

</details>

#### single-char-flip input changes the result (discrimination)

- single-char-flip input changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char-flip input changes the result (discrimination)")
assert_true(to_upper_ascii("abc") != to_upper_ascii("abd"))
assert_true(rt_text_to_upper_ascii("abc") != rt_text_to_upper_ascii("abd"))
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
assert_equal(to_upper_ascii("repeat me"), to_upper_ascii("repeat me"))
assert_equal(rt_text_to_upper_ascii("repeat me"), rt_text_to_upper_ascii("repeat me"))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val lower = "abcdefghijklmnopqrstuvwxyz"
val upper_mix = "AbCdEfGhIjKlMnOpQrStUvWxYz 0123456789 !@#"
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val len_choice = seed % 5

    var s = ""
    if len_choice == 0:
        s = ""                       # empty
    else if len_choice == 1:
        s = lower.substring(0, 1 + (seed % 26))   # lowercase-only run
    else if len_choice == 2:
        s = upper_mix                              # fixed mixed corpus
    else if len_choice == 3:
        s = lower.substring(seed % 26, 26)         # lowercase suffix
    else:
        s = "  " + lower.substring(0, 1 + (seed % 10)) + "  "  # whitespace-padded

    val t0 = time_now_unix_micros()
    val sr = to_upper_ascii(s)
    val t1 = time_now_unix_micros()
    val cr = rt_text_to_upper_ascii(s)
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
| Source | `test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering to_upper_ascii — pure-Simple vs Rust-interpreter oracle (rt_text_to_upper_ascii).
- to_upper_ascii — pure-Simple vs Rust-interpreter oracle (rt_text_to_upper_ascii)

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
- `REQ-C-MIG-TEXT-TO-UPPER-ASCII`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4745d1c73ef41a1192499e915c2c240a683e7af26e8633ad8a7749f702779c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4745d1c73ef41a1192499e915c2c240a683e7af26e8633ad8a7749f702779c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4745d1c73ef41a1192499e915c2c240a683e7af26e8633ad8a7749f702779c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char-flip input changes the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
