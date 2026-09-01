# Ascii Pure Ext Crosslang Specification

> Tests covering is_ascii_text — pure-Simple vs Rust-interpreter oracle (rt_text_is_ascii).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ascii Pure Ext Crosslang Specification

## Scenarios

### is_ascii_text — pure-Simple vs Rust-interpreter oracle (rt_text_is_ascii)

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
assert_equal(is_ascii_text("hello"), true)
assert_equal(is_ascii_text("hello"), rt_text_is_ascii("hello"))
assert_equal(is_ascii_text("Hello, World! 123"), true)
assert_equal(is_ascii_text("Hello, World! 123"), rt_text_is_ascii("Hello, World! 123"))
assert_equal(is_ascii_text("café"), false)
assert_equal(is_ascii_text("café"), rt_text_is_ascii("café"))
assert_equal(is_ascii_text("日本語"), false)
assert_equal(is_ascii_text("日本語"), rt_text_is_ascii("日本語"))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# Empty string: vacuously ASCII.
assert_equal(is_ascii_text(""), true)
assert_equal(is_ascii_text(""), rt_text_is_ascii(""))

# Single ASCII byte-class boundaries: 0x00 (NUL), 0x7F (DEL) are
# both ASCII; a leading byte >= 0x80 is never ASCII.
assert_equal(is_ascii_text("\u{0}"), true)
assert_equal(is_ascii_text("\u{0}"), rt_text_is_ascii("\u{0}"))
assert_equal(is_ascii_text("\u{7f}"), true)
assert_equal(is_ascii_text("\u{7f}"), rt_text_is_ascii("\u{7f}"))

# A single 2-byte UTF-8 codepoint just past the ASCII boundary
# (U+0080, first byte 0xC2 >= 0x80): not ASCII.
assert_equal(is_ascii_text("\u{80}"), false)
assert_equal(is_ascii_text("\u{80}"), rt_text_is_ascii("\u{80}"))

# Non-ASCII char at the very end of an otherwise-ASCII string.
assert_equal(is_ascii_text("abcé"), false)
assert_equal(is_ascii_text("abcé"), rt_text_is_ascii("abcé"))

# Non-ASCII char at the very start.
assert_equal(is_ascii_text("éabc"), false)
assert_equal(is_ascii_text("éabc"), rt_text_is_ascii("éabc"))

# All-whitespace ASCII input (space, tab, newline are all ASCII).
assert_equal(is_ascii_text("  \t\n "), true)
assert_equal(is_ascii_text("  \t\n "), rt_text_is_ascii("  \t\n "))

# 4-byte UTF-8 codepoint (emoji, astral plane): not ASCII.
assert_equal(is_ascii_text("😀"), false)
assert_equal(is_ascii_text("😀"), rt_text_is_ascii("😀"))

# Long all-ASCII run (boundary-adjacent length, no multibyte).
assert_equal(is_ascii_text("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), true)
assert_equal(is_ascii_text("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), rt_text_is_ascii("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"))
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
assert_true(is_ascii_text("abc") != is_ascii_text("abé"))
assert_true(rt_text_is_ascii("abc") != rt_text_is_ascii("abé"))
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
assert_equal(is_ascii_text("mixed é text"), is_ascii_text("mixed é text"))
assert_equal(rt_text_is_ascii("mixed é text"), rt_text_is_ascii("mixed é text"))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val fragments = ["hello", "world", "123", "  ", "", "abc", "!@#", "XYZ"]
val nonascii = ["é", "日", "😀", "ñ", "\u{80}", "\u{7f}"]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val base = fragments[seed % 8]
    var p = base
    if i % 4 == 0:
        p = base + nonascii[seed % 6]      # non-ASCII appended
    else if i % 6 == 0:
        p = nonascii[seed % 6] + base       # non-ASCII prepended
    else if i % 9 == 0:
        p = base + base                     # doubled, still ASCII

    val t0 = time_now_unix_micros()
    val sr = is_ascii_text(p)
    val t1 = time_now_unix_micros()
    val cr = rt_text_is_ascii(p)
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
| Source | `test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering is_ascii_text — pure-Simple vs Rust-interpreter oracle (rt_text_is_ascii).
- is_ascii_text — pure-Simple vs Rust-interpreter oracle (rt_text_is_ascii)

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
- `REQ-C-MIG-ASCII-IS-ASCII`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ebe93214eee35082a24b6636c4ee4c988e9de9be42e3ed3c78ae7863ae66631`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ebe93214eee35082a24b6636c4ee4c988e9de9be42e3ed3c78ae7863ae66631`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ebe93214eee35082a24b6636c4ee4c988e9de9be42e3ed3c78ae7863ae66631`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ascii_pure_ext_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/ascii_pure_ext_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ascii_pure_ext_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ascii_pure_ext_crosslang_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char input change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
