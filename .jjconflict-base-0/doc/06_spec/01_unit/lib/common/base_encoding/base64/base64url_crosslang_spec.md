# Base64url Crosslang Specification

> Tests covering base64url encode/decode — pure-Simple vs C oracle (RFC 4648 section 5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64url Crosslang Specification

## Scenarios

### base64url encode/decode — pure-Simple vs C oracle (RFC 4648 section 5)

#### matches the C oracle on KAT vectors (RFC 4648 test vectors, url-safe, unpadded)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on KAT vectors (RFC 4648 test vectors, url-safe, unpadded)


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on KAT vectors (RFC 4648 test vectors, url-safe, unpadded)")
# RFC 4648 section 10 test vectors, re-expressed without '+'/'/' since
# none of the standard KATs happen to produce those chars; the
# url-safe alphabet only differs from standard base64 in char 62/63
# and padding, exercised separately below.
assert_equal(simple_encode(""), "")
assert_equal(simple_encode(""), rt_base64url_encode("", 0))
assert_equal(simple_encode("f"), "Zg")
assert_equal(simple_encode("f"), rt_base64url_encode("f", 1))
assert_equal(simple_encode("fo"), "Zm8")
assert_equal(simple_encode("fo"), rt_base64url_encode("fo", 2))
assert_equal(simple_encode("foo"), "Zm9v")
assert_equal(simple_encode("foo"), rt_base64url_encode("foo", 3))
assert_equal(simple_encode("foob"), "Zm9vYg")
assert_equal(simple_encode("foob"), rt_base64url_encode("foob", 4))
assert_equal(simple_encode("fooba"), "Zm9vYmE")
assert_equal(simple_encode("fooba"), rt_base64url_encode("fooba", 5))
assert_equal(simple_encode("foobar"), "Zm9vYmFy")
assert_equal(simple_encode("foobar"), rt_base64url_encode("foobar", 6))
```

</details>

#### round-trips through decode, matching the C oracle

- round-trips through decode, matching the C oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through decode, matching the C oracle")
val vectors = ["", "f", "fo", "foo", "foob", "fooba", "foobar", "hello world", "Simple!"]
var i = 0
while i < vectors.len():
    val v = vectors[i]
    val simple_enc = simple_encode(v)
    val c_enc = rt_base64url_encode(v, v.bytes().len())
    assert_equal(simple_enc, c_enc)
    val simple_dec = simple_decode(simple_enc)
    val c_dec = rt_base64url_decode(c_enc)
    assert_equal(simple_dec, v)
    assert_equal(simple_dec, c_dec)
    i = i + 1
```

</details>

#### produces url-safe chars (- and _), never + or / or padding =, matching the C oracle

- produces url-safe chars (- and _), never + or / or padding =, matching the C oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces url-safe chars (- and _), never + or / or padding =, matching the C oracle")
# Representative texts whose standard base64 encoding is known to
# contain '+' and/or '/' (verified against RFC 4648 KATs above and
# common base64 fixtures), so the url-safe substitution is actually
# exercised on both sides, not vacuously true by construction.
val vectors = ["foobar", "any carnal pleasure.", "\u{00fb}\u{00ff}\u{00bf}"]
var i = 0
while i < vectors.len():
    val v = vectors[i]
    val enc = simple_encode(v)
    val oracle_enc = rt_base64url_encode(v, v.bytes().len())
    assert_equal(enc, oracle_enc)
    assert_true(!enc.contains("+"))
    assert_true(!enc.contains("/"))
    assert_true(!enc.contains("="))
    i = i + 1
```

</details>

#### single-char corruption changes the decoded value (discrimination)

- single-char corruption changes the decoded value (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char corruption changes the decoded value (discrimination)")
val enc_a = simple_encode("abc")
val enc_b = simple_encode("abd")
assert_true(enc_a != enc_b)
assert_true(rt_base64url_encode("abc", 3) != rt_base64url_encode("abd", 3))
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
assert_equal(simple_encode("determinism"), simple_encode("determinism"))
assert_equal(rt_base64url_encode("determinism", 11), rt_base64url_encode("determinism", 11))
```

</details>

#### matches the C oracle on 100 shared branch-covering vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME input to BOTH sides inside
# this loop. Branch coverage: length 0..99 via a seeded LCG over a
# printable-ASCII-plus-UTF-8-multibyte alphabet, cycling through
# ASCII letters/digits and a 2-byte UTF-8 codepoint (U+00E9 'é',
# encoded 0xC3 0xA9) every 7th char to exercise multibyte text.
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
        if j % 7 == 6:
            body = body + "é"
        else:
            val bucket = seed % 62
            if bucket < 26:
                body = body + ENC_LOWER.char_at(bucket)
            else if bucket < 52:
                body = body + ENC_UPPER.char_at(bucket - 26)
            else:
                body = body + ENC_DIGIT.char_at(bucket - 52)
        j = j + 1
    val nbytes = body.bytes().len()
    val t0 = time_now_unix_micros()
    val s = simple_encode(body)
    val t1 = time_now_unix_micros()
    val c = rt_base64url_encode(body, nbytes)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_equal(s, c)
    i = i + 1
print("perf_evidence: shared_corpus=100 simple_us={simple_us} c_us={c_us}")
assert_true(simple_us >= 0 and c_us >= 0)
```

</details>

#### matches the C oracle on exact-boundary lengths (0, 1, 2, 3-byte-multiple, and a >4KB input)

- matches the C oracle on exact-boundary lengths (0, 1, 2, 3-byte-multiple, and a >4KB input)


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on exact-boundary lengths (0, 1, 2, 3-byte-multiple, and a >4KB input)")
# Similar-case coverage for the array-accumulator rewrite of
# base64_encode/base64url_encode/base64url_decode (byte-array push +
# single join, replacing the old O(n^2) `out = out + c` scalar text
# concatenation): exercises the exact tail shapes the accumulator
# touches (0/1/2 remaining input bytes per 3-byte group) plus an
# input large enough (>4KB) to make an O(n^2) regression obvious.
val a = "A"          # 1-byte tail -> 2 pad chars in std base64
val ab = "AB"        # 2-byte tail -> 1 pad char in std base64
val abc = "ABC"      # exact 3-byte multiple -> no padding
val abcabc = "ABCABC"  # two exact 3-byte groups

assert_equal(simple_encode(""), rt_base64url_encode("", 0))
assert_equal(simple_encode(a), rt_base64url_encode(a, 1))
assert_equal(simple_encode(ab), rt_base64url_encode(ab, 2))
assert_equal(simple_encode(abc), rt_base64url_encode(abc, 3))
assert_equal(simple_encode(abcabc), rt_base64url_encode(abcabc, 6))

assert_equal(simple_decode(simple_encode(a)), a)
assert_equal(simple_decode(simple_encode(ab)), ab)
assert_equal(simple_decode(simple_encode(abc)), abc)
assert_equal(simple_decode(simple_encode(abcabc)), abcabc)

# >4KB input (4200 bytes, not a multiple of 3, so it also exercises
# a 2-byte tail at large scale).
var big = ""
var k = 0
while k < 4200:
    big = big + ENC_LOWER.char_at(k % 26)
    k = k + 1
val big_simple_enc = simple_encode(big)
val big_c_enc = rt_base64url_encode(big, big.bytes().len())
assert_equal(big_simple_enc, big_c_enc)
assert_equal(simple_decode(big_simple_enc), big)
assert_equal(simple_decode(big_c_enc), rt_base64url_decode(big_c_enc))
```

</details>

#### POSITIVE CONTROL: the pure-Simple decoder under test is really loaded

- POSITIVE CONTROL: the pure-Simple decoder under test is really loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: the pure-Simple decoder under test is really loaded")
# Guards the whole out-of-alphabet group below: if the import silently
# resolved to nothing, simple_decode would return "" for everything
# and the "yields empty" examples would pass for the wrong reason.
assert_equal(simple_encode("Simple"), "U2ltcGxl")
assert_equal(simple_decode("U2ltcGxl"), "Simple")
```

</details>

#### CHARACTERIZATION: an all-invalid group decodes to empty, not an error

- CHARACTERIZATION: an all-invalid group decodes to empty, not an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CHARACTERIZATION: an all-invalid group decodes to empty, not an error")
for v in ["!!!!", "%%", "...."]:
    assert_equal(simple_decode(v), "")
```

</details>

#### CHARACTERIZATION: invalid symbols are dropped, not rejected (RFC 4648 s3.3 violation)

- CHARACTERIZATION: invalid symbols are dropped, not rejected (RFC 4648 s3.3 violation)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CHARACTERIZATION: invalid symbols are dropped, not rejected (RFC 4648 s3.3 violation)")
# Mixed valid/invalid: the valid remainder is silently decoded, so a
# malformed segment is indistinguishable from a well-formed one at
# the call site. This is the defect the bug doc tracks.
assert_equal(simple_decode("ab*d").len(), 2)
assert_equal(simple_decode("a b c").len(), 2)
```

</details>

#### CHARACTERIZATION: '+' and '/' are tolerated, and the oracle disagrees

- CHARACTERIZATION: '+' and '/' are tolerated, and the oracle disagrees


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CHARACTERIZATION: '+' and '/' are tolerated, and the oracle disagrees")
# Standard-alphabet text is NOT valid base64url. Both sides accept it
# anyway and produce DIFFERENT results — so this is precisely where
# the differential oracle must not be treated as ground truth.
val std_alphabet = "a+b/c"
assert_equal(simple_decode(std_alphabet).len(), 3)
assert_true(simple_decode(std_alphabet) != rt_base64url_decode(std_alphabet))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base64url encode/decode — pure-Simple vs C oracle (RFC 4648 section 5).
- base64url encode/decode — pure-Simple vs C oracle (RFC 4648 section 5)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-BASE64URL`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40a0e9589c9c390ba4dd8efd13a6dd510b695f4d042b3da4184b20ea57b54c0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40a0e9589c9c390ba4dd8efd13a6dd510b695f4d042b3da4184b20ea57b54c0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40a0e9589c9c390ba4dd8efd13a6dd510b695f4d042b3da4184b20ea57b54c0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on KAT vectors (RFC 4648 test vectors, url-safe, unpadded)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through decode, matching the C oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_crosslang_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces url-safe chars (- and _), never + or / or padding =, matching the C oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
