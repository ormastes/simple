# String Core Char From Code Crosslang Specification

> Tests covering char_from_code — pure-Simple vs C oracle (rt_char_from_code).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Char From Code Crosslang Specification

## Scenarios

### char_from_code — pure-Simple vs C oracle (rt_char_from_code)

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
assert_equal(char_from_code(65), "A")
assert_equal(char_from_code(65), rt_char_from_code(65))
assert_equal(char_from_code(48), "0")
assert_equal(char_from_code(48), rt_char_from_code(48))
assert_equal(char_from_code(32), " ")
assert_equal(char_from_code(32), rt_char_from_code(32))
assert_equal(char_from_code(9), "\t")
assert_equal(char_from_code(9), rt_char_from_code(9))
assert_equal(char_from_code(10), "\n")
assert_equal(char_from_code(10), rt_char_from_code(10))
assert_equal(char_from_code(126), "~")
assert_equal(char_from_code(126), rt_char_from_code(126))
```

</details>

#### matches the C oracle on multibyte UTF-8 codepoints

- matches the C oracle on multibyte UTF-8 codepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on multibyte UTF-8 codepoints")
# 2-byte (e acute U+00E9), 3-byte (euro sign U+20AC), 4-byte
# (grinning face emoji U+1F600) codepoints — each encoding class the
# UTF-8 byte math branches on.
assert_equal(char_from_code(233), "\u{e9}")
assert_equal(char_from_code(233), rt_char_from_code(233))
assert_equal(char_from_code(0x20AC), "\u{20AC}")
assert_equal(char_from_code(0x20AC), rt_char_from_code(0x20AC))
assert_equal(char_from_code(0x1F600), "\u{1F600}")
assert_equal(char_from_code(0x1F600), rt_char_from_code(0x1F600))
```

</details>

#### matches the C oracle on invalid-codepoint edge cases (both collapse to empty)

- matches the C oracle on invalid-codepoint edge cases (both collapse to empty)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on invalid-codepoint edge cases (both collapse to empty)")
assert_equal(char_from_code(-1), "")
assert_equal(char_from_code(-1), rt_char_from_code(-1))
assert_equal(char_from_code(0x110000), "")
assert_equal(char_from_code(0x110000), rt_char_from_code(0x110000))
# Surrogate range U+D800..U+DFFF is invalid as a scalar value.
assert_equal(char_from_code(0xD800), "")
assert_equal(char_from_code(0xD800), rt_char_from_code(0xD800))
assert_equal(char_from_code(0xDFFF), "")
assert_equal(char_from_code(0xDFFF), rt_char_from_code(0xDFFF))
# Boundary just outside the surrogate range must still succeed.
assert_equal(char_from_code(0xD7FF), rt_char_from_code(0xD7FF))
assert_equal(char_from_code(0xE000), rt_char_from_code(0xE000))
# U+10FFFF is the maximum valid scalar value.
assert_equal(char_from_code(0x10FFFF), rt_char_from_code(0x10FFFF))
```

</details>

#### single-codepoint corruption changes the result (discrimination)

- single-codepoint corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-codepoint corruption changes the result (discrimination)")
assert_true(char_from_code(65) != char_from_code(66))
assert_true(rt_char_from_code(65) != rt_char_from_code(66))
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
assert_equal(char_from_code(233), char_from_code(233))
assert_equal(rt_char_from_code(233), rt_char_from_code(233))
```

</details>

#### matches the C oracle on 100 shared branch-covering vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME codepoint to BOTH sides
# inside this loop. Branch coverage via a seeded LCG cycling through
# every encoding-length class (1-byte ASCII, 2-byte, 3-byte, 4-byte),
# plus the invalid-scalar classes (negative, > 0x10FFFF, surrogate
# range) at fixed moduli so every rejection branch is exercised too.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var code = 0
    if i % 13 == 0:
        code = -1 - (seed % 1000)
    else if i % 11 == 0:
        code = 0x110000 + (seed % 1000)
    else if i % 7 == 0:
        code = 0xD800 + (seed % (0xDFFF - 0xD800 + 1))
    else:
        val class_pick = seed % 4
        if class_pick == 0:
            code = seed % 0x80
        else if class_pick == 1:
            code = 0x80 + (seed % (0x800 - 0x80))
        else if class_pick == 2:
            code = 0x800 + (seed % (0xD800 - 0x800))
        else:
            code = 0x10000 + (seed % (0x10FFFF - 0x10000 + 1))

    val t0 = time_now_unix_micros()
    val s = char_from_code(code)
    val t1 = time_now_unix_micros()
    val c = rt_char_from_code(code)
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
| Source | `test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering char_from_code — pure-Simple vs C oracle (rt_char_from_code).
- char_from_code — pure-Simple vs C oracle (rt_char_from_code)

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
- `REQ-C-MIG-CHAR-FROM-CODE`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2056b689ee83287e6c7f63363b23ea1f028b112a394aadd11169c790d12176b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2056b689ee83287e6c7f63363b23ea1f028b112a394aadd11169c790d12176b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2056b689ee83287e6c7f63363b23ea1f028b112a394aadd11169c790d12176b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_core_char_from_code_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/string_core_char_from_code_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_core_char_from_code_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on published-shape KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on multibyte UTF-8 codepoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_char_from_code_crosslang_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on invalid-codepoint edge cases (both collapse to empty)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
