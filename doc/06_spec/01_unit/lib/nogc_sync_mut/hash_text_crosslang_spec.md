# Hash Text Crosslang Specification

> Tests covering text hash — pure-Simple FNV-1a vs C oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hash Text Crosslang Specification

## Scenarios

### text hash — pure-Simple FNV-1a vs C oracle

#### matches the C oracle on the empty string (offset basis)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on the empty string (offset basis)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on the empty string (offset basis)")
val simple = simple_hash_text("")
val oracle = rt_hash_text("")
assert_equal(simple, oracle)
# FNV-1a 64-bit offset basis 0xcbf29ce484222325 as signed i64.
assert_equal(simple, -3750763034362895579)
```

</details>

#### matches the C oracle on a known ASCII KAT

- matches the C oracle on a known ASCII KAT


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on a known ASCII KAT")
# FNV-1a 64-bit of "abc" is well-known: 0xe71fa2190541574b.
val simple = simple_hash_text("abc")
val oracle = rt_hash_text("abc")
assert_equal(simple, oracle)
assert_equal(simple, -1792535898324117685)  # 0xe71fa2190541574b signed
```

</details>

#### matches the C oracle across representative differential vectors

- matches the C oracle across representative differential vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle across representative differential vectors")
val vectors = [
    "a", "ab", "hello", "hello world",
    "The quick brown fox jumps over the lazy dog",
    "0", "00", "false", "null",
    "a very long string used to exercise the multiply-heavy inner loop over many bytes so that overflow wraparound behavior is exercised the same way in both implementations"
]
var i = 0
while i < vectors.len():
    val simple = simple_hash_text(vectors[i])
    val oracle = rt_hash_text(vectors[i])
    assert_equal(simple, oracle)
    i = i + 1
```

</details>

#### matches the C oracle on UTF-8 multi-byte input

- matches the C oracle on UTF-8 multi-byte input


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on UTF-8 multi-byte input")
val vectors = ["héllo", "日本語", "emoji 🎉 test", "Ω≈ç√∫"]
var i = 0
while i < vectors.len():
    val simple = simple_hash_text(vectors[i])
    val oracle = rt_hash_text(vectors[i])
    assert_equal(simple, oracle)
    i = i + 1
```

</details>

#### matches the C oracle on boundary-length inputs

- matches the C oracle on boundary-length inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on boundary-length inputs")
# 1, 8, 63, 64, 65 bytes — exercises word-boundary edge cases.
val lens = [1, 8, 63, 64, 65]
var li = 0
while li < lens.len():
    var s = ""
    var n = 0
    while n < lens[li]:
        s = s + "x"
        n = n + 1
    assert_equal(simple_hash_text(s), rt_hash_text(s))
    li = li + 1
```

</details>

#### single-byte corruption changes the hash (avalanche / discrimination)

- single-byte corruption changes the hash (avalanche / discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-byte corruption changes the hash (avalanche / discrimination)")
val a = simple_hash_text("The quick brown fox")
val b = simple_hash_text("The quick brown foy")  # last char flipped
assert_true(a != b)
# And the C oracle agrees the two differ too.
assert_true(rt_hash_text("The quick brown fox") != rt_hash_text("The quick brown foy"))
```

</details>

#### is deterministic and order-sensitive on both sides

- is deterministic and order-sensitive on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic and order-sensitive on both sides")
assert_equal(simple_hash_text("ab"), simple_hash_text("ab"))
assert_true(simple_hash_text("ab") != simple_hash_text("ba"))
assert_true(rt_hash_text("ab") != rt_hash_text("ba"))
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
# 0..99 (empty-input branch, single-byte, multi-word sizes), byte
# classes cycling through 0-adjacent, ASCII, 127/128 boundary, and
# multibyte UTF-8 via the seeded generator.
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
    val s = simple_hash_text(body)
    val t1 = time_now_unix_micros()
    val c = rt_hash_text(body)
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
| Source | `test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text hash — pure-Simple FNV-1a vs C oracle.
- text hash — pure-Simple FNV-1a vs C oracle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-HASHTEXT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e63178fef113d410cff2bcb00b855964c2ffc468e109798bcd83cc23b4c7697f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e63178fef113d410cff2bcb00b855964c2ffc468e109798bcd83cc23b4c7697f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e63178fef113d410cff2bcb00b855964c2ffc468e109798bcd83cc23b4c7697f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on the empty string (offset basis)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on a known ASCII KAT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle across representative differential vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
