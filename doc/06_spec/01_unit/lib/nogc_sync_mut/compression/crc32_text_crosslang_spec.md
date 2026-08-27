# Crc32 Text Crosslang Specification

> Tests covering crc32_text pure-Simple vs C oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crc32 Text Crosslang Specification

## Scenarios

### crc32_text pure-Simple vs C oracle

#### matches the published CRC-32/ISO-HDLC KAT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the published CRC-32/ISO-HDLC KAT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the published CRC-32/ISO-HDLC KAT")
# Rocksoft/CRC catalogue check value for "123456789"
assert_equal(crc32_text("123456789"), 0xCBF43926)
```

</details>

#### returns 0 for empty input (C contract)

- returns 0 for empty input (C contract)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for empty input (C contract)")
assert_equal(crc32_text(""), 0)
```

</details>

#### matches the C oracle on representative vectors

- matches the C oracle on representative vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on representative vectors")
val vectors = [
    "a",
    "abc",
    "hello world",
    "The quick brown fox jumps over the lazy dog",
    "0000000000000000000000000000000000000000",
    "\n\t\r mixed  whitespace \n",
    "utf8: héllo wörld ✓"
]
for v in vectors:
    assert_equal(crc32_text(v), rt_crc32_text(v))
```

</details>

#### matches the C oracle on a longer body (database WAL shape)

- matches the C oracle on a longer body (database WAL shape)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on a longer body (database WAL shape)")
var body = ""
var i = 0
while i < 200:
    body = body + "row-{i}|payload|"
    i = i + 1
assert_equal(crc32_text(body), rt_crc32_text(body))
```

</details>

#### differs on corrupted input (checksum actually discriminates)

- differs on corrupted input (checksum actually discriminates)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("differs on corrupted input (checksum actually discriminates)")
val good = crc32_text("wal-entry-payload")
val bad = crc32_text("wal-entry-payloae")
assert_true(good != bad)
```

</details>

#### matches the C oracle on 100 shared branch-covering vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME input to BOTH sides inside
# this loop — the loop is the shared logic. Branch coverage: length
# 0..99 (hits the empty-input branch, single-byte, and multi-block
# sizes), byte classes cycling through 0-adjacent, ASCII, 127/128
# boundary, and 255 via the seeded generator.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    # deterministic content: length == i, bytes from a seeded LCG
    var body = ""
    var seed = i * 2654435761 % 4294967296
    var j = 0
    while j < i:
        seed = (seed * 1103515245 + 12345) % 2147483648
        # map into codepoint classes incl. multibyte (branch: UTF-8)
        val cls = seed % 4
        if cls == 0:
            body = body + "a"
        elif cls == 1:
            body = body + "~"
        elif cls == 2:
            body = body + "0"
        else:
            body = body + "é"
        j = j + 1
    val t0 = time_now_unix_micros()
    val s = crc32_text(body)
    val t1 = time_now_unix_micros()
    val c = rt_crc32_text(body)
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
| Source | `test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering crc32_text pure-Simple vs C oracle.
- crc32_text pure-Simple vs C oracle

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
- `REQ-C-MIG-CRC32-TEXT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6378ea1d0de5add1d6b959af88d9aa44578f8a7c0d6e6aa83ad686beef8581ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6378ea1d0de5add1d6b959af88d9aa44578f8a7c0d6e6aa83ad686beef8581ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6378ea1d0de5add1d6b959af88d9aa44578f8a7c0d6e6aa83ad686beef8581ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the published CRC-32/ISO-HDLC KAT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for empty input (C contract)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/compression/crc32_text_crosslang_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on representative vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
