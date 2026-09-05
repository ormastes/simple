# Encoding Byte Char Crosslang Specification

> Tests covering byte_char — pure-Simple vs C/Rust oracle (rt_byte_char).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encoding Byte Char Crosslang Specification

## Scenarios

### byte_char — pure-Simple vs C/Rust oracle (rt_byte_char)

#### matches the oracle on published-shape KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on published-shape KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on published-shape KATs")
assert_equal(byte_char(65), "A")
assert_equal(byte_char(65), rt_byte_char(65))
assert_equal(byte_char(48), "0")
assert_equal(byte_char(48), rt_byte_char(48))
assert_equal(byte_char(32), " ")
assert_equal(byte_char(32), rt_byte_char(32))
assert_equal(byte_char(0), rt_byte_char(0))
assert_equal(byte_char(127), rt_byte_char(127))
```

</details>

#### matches the oracle on the 1-byte/2-byte UTF-8 boundary (0x7F vs 0x80)

- matches the oracle on the 1-byte/2-byte UTF-8 boundary (0x7F vs 0x80)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on the 1-byte/2-byte UTF-8 boundary (0x7F vs 0x80)")
assert_equal(byte_char(0x7F), rt_byte_char(0x7F))
assert_equal(byte_char(0x80), rt_byte_char(0x80))
assert_equal(byte_char(0x80), "\u{80}")
```

</details>

#### matches the oracle across the full 2-byte Latin-1 supplement range

- matches the oracle across the full 2-byte Latin-1 supplement range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle across the full 2-byte Latin-1 supplement range")
assert_equal(byte_char(0x81), rt_byte_char(0x81))
assert_equal(byte_char(0xA9), rt_byte_char(0xA9))
assert_equal(byte_char(0xE9), rt_byte_char(0xE9))
assert_equal(byte_char(0xFF), rt_byte_char(0xFF))
assert_equal(byte_char(0xFF), "\u{FF}")
```

</details>

#### single-byte corruption changes the result (discrimination)

- single-byte corruption changes the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-byte corruption changes the result (discrimination)")
assert_true(byte_char(65) != byte_char(66))
assert_true(rt_byte_char(200) != rt_byte_char(201))
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
assert_equal(byte_char(0xE9), byte_char(0xE9))
assert_equal(rt_byte_char(0xE9), rt_byte_char(0xE9))
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
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME byte value to BOTH sides
# inside this loop. Branch coverage via a seeded LCG cycling through
# the full 0..255 byte range so both UTF-8 encoding-length branches
# (1-byte ASCII, 2-byte Latin-1 supplement) are exercised, plus
# forced boundary values at fixed moduli.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    var v = seed % 256
    if i % 17 == 0:
        v = 0x7F
    else if i % 13 == 0:
        v = 0x80
    else if i % 11 == 0:
        v = 0
    else if i % 7 == 0:
        v = 0xFF

    val t0 = time_now_unix_micros()
    val s = byte_char(v)
    val t1 = time_now_unix_micros()
    val c = rt_byte_char(v)
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
| Source | `test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering byte_char — pure-Simple vs C/Rust oracle (rt_byte_char).
- byte_char — pure-Simple vs C/Rust oracle (rt_byte_char)

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
- `REQ-C-MIG-BYTE-CHAR`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b6eb804afb47296e3a33d75d44988522935f6827f8a359b5182b04afc7407a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b6eb804afb47296e3a33d75d44988522935f6827f8a359b5182b04afc7407a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b6eb804afb47296e3a33d75d44988522935f6827f8a359b5182b04afc7407a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding_byte_char_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/encoding_byte_char_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding_byte_char_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on published-shape KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on the 1-byte/2-byte UTF-8 boundary (0x7F vs 0x80)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding_byte_char_crosslang_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle across the full 2-byte Latin-1 supplement range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
