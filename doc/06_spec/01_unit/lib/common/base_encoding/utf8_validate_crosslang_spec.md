# Utf8 Validate Crosslang Specification

> Tests covering UTF-8 validation — pure-Simple vs C oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf8 Validate Crosslang Specification

## Scenarios

### UTF-8 validation — pure-Simple vs C oracle

#### matches the C oracle on empty string and ASCII

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on empty string and ASCII


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on empty string and ASCII")
assert_equal(simple_is_valid_utf8(""), rt_text_validate_utf8(""))
assert_true(simple_is_valid_utf8(""))
assert_true(rt_text_validate_utf8(""))
assert_equal(simple_is_valid_utf8("hello"), rt_text_validate_utf8("hello"))
assert_true(simple_is_valid_utf8("hello"))
```

</details>

#### matches the C oracle on valid UTF-8 multi-byte input

- matches the C oracle on valid UTF-8 multi-byte input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on valid UTF-8 multi-byte input")
val vectors = ["héllo", "日本語", "emoji 🎉 test", "Ω≈ç√∫", "Café MENU", "👍👎🎉"]
var i = 0
while i < vectors.len():
    assert_equal(simple_is_valid_utf8(vectors[i]), rt_text_validate_utf8(vectors[i]))
    assert_true(simple_is_valid_utf8(vectors[i]))
    i = i + 1
```

</details>

#### the pure-Simple validator rejects malformed byte sequences (discrimination)

- the pure-Simple validator rejects malformed byte sequences (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the pure-Simple validator rejects malformed byte sequences (discrimination)")
val invalid = build_invalid_byte_vectors()
var i = 0
while i < invalid.len():
    match validated_utf8_bytes_to_text_linear(invalid[i]):
        Ok(_decoded):
            assert_true(false)
        Err(_error):
            assert_true(true)
    i = i + 1
```

</details>

<details>
<summary>Advanced: runs a shared-logic bulk differential loop over ~90 branch-covering valid vectors, and measures perf</summary>

#### runs a shared-logic bulk differential loop over ~90 branch-covering valid vectors, and measures perf

- runs a shared-logic bulk differential loop over ~90 branch-covering valid vectors, and measures perf


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs a shared-logic bulk differential loop over ~90 branch-covering valid vectors, and measures perf")
val vectors = build_bulk_vectors()
assert_true(vectors.len() >= 85)

# --- shared differential loop: same input feeds BOTH implementations ---
var i = 0
while i < vectors.len():
    val v = vectors[i]
    assert_equal(simple_is_valid_utf8(v), rt_text_validate_utf8(v))
    assert_true(simple_is_valid_utf8(v))
    i = i + 1

# --- perf: time both sides over the same corpus ---
val simple_start = time_now_unix_micros()
var si = 0
while si < vectors.len():
    simple_is_valid_utf8(vectors[si])
    si = si + 1
val simple_end = time_now_unix_micros()
val simple_micros = simple_end - simple_start

val c_start = time_now_unix_micros()
var ci = 0
while ci < vectors.len():
    rt_text_validate_utf8(vectors[ci])
    ci = ci + 1
val c_end = time_now_unix_micros()
val c_micros = c_end - c_start

print("perf_evidence: simple_micros={simple_micros} c_micros={c_micros} vectors={vectors.len()}")
assert_true(simple_micros >= 0)
assert_true(c_micros >= 0)
```

</details>


</details>

#### matches the C oracle on batched-ASCII fast-path boundary shapes

- matches the C oracle on batched-ASCII fast-path boundary shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on batched-ASCII fast-path boundary shapes")
# Long pure-ASCII run — exercises the inner fast-path loop end to end.
var long_ascii = ""
var li = 0
while li < 300:
    long_ascii = long_ascii + "x"
    li = li + 1
assert_equal(simple_is_valid_utf8(long_ascii), rt_text_validate_utf8(long_ascii))
assert_true(simple_is_valid_utf8(long_ascii))

# High byte at position 0 (no ASCII run before the multibyte lead).
val high_at_start = "é" + long_ascii
assert_equal(simple_is_valid_utf8(high_at_start), rt_text_validate_utf8(high_at_start))
assert_true(simple_is_valid_utf8(high_at_start))

# High byte at the very last position (fast path runs to the end,
# then the outer loop must still see the trailing multibyte char).
val high_at_end = long_ascii + "é"
assert_equal(simple_is_valid_utf8(high_at_end), rt_text_validate_utf8(high_at_end))
assert_true(simple_is_valid_utf8(high_at_end))

# High byte straddling likely fast-path chunk boundaries (64/128/256).
var i = 60
while i <= 260:
    var s = ""
    var k = 0
    while k < i:
        s = s + "x"
        k = k + 1
    s = s + "日" + long_ascii
    assert_equal(simple_is_valid_utf8(s), rt_text_validate_utf8(s))
    assert_true(simple_is_valid_utf8(s))
    i = i + 1

# Alternating ASCII / multibyte — forces the fast path to kick in and
# bail out repeatedly within one buffer.
var alt = ""
var ai = 0
while ai < 40:
    alt = alt + "ab" + "日" + "cd" + "🎉"
    ai = ai + 1
assert_equal(simple_is_valid_utf8(alt), rt_text_validate_utf8(alt))
assert_true(simple_is_valid_utf8(alt))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UTF-8 validation — pure-Simple vs C oracle.
- UTF-8 validation — pure-Simple vs C oracle

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
- `REQ-C-MIG-UTF8VALIDATE`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a944bafdf9c4bdb1144a21109c84f9cd4e79d2ab30e60830e963bf7477927db1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a944bafdf9c4bdb1144a21109c84f9cd4e79d2ab30e60830e963bf7477927db1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a944bafdf9c4bdb1144a21109c84f9cd4e79d2ab30e60830e963bf7477927db1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on empty string and ASCII' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on valid UTF-8 multi-byte input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/utf8_validate_crosslang_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the pure-Simple validator rejects malformed byte sequences (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
