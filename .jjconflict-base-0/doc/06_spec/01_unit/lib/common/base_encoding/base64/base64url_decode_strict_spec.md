# Base64url Decode Strict Specification

> Tests covering base64url_decode_strict — rejects out-of-alphabet input (RFC 4648 s3.3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64url Decode Strict Specification

## Scenarios

### base64url_decode_strict — rejects out-of-alphabet input (RFC 4648 s3.3)

#### POSITIVE CONTROL: the strict decoder under test is really loaded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: the strict decoder under test is really loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: the strict decoder under test is really loaded")
# If the import silently resolved to nothing, every `is_ok() == false`
# assertion below could pass for the wrong reason. This example fails
# RED on a wrong/missing import, because it demands a SUCCESSFUL
# decode with an exact payload, which no absent/sentinel value gives.
val r = base64url_decode_strict("U2ltcGxl")
assert_equal(r.is_ok(), true)
assert_equal(r.unwrap(), "Simple")
assert_equal(base64url_encode("Simple"), "U2ltcGxl")
```

</details>

#### REPRODUCING: all-invalid groups are rejected (lenient one returns empty)

- REPRODUCING: all-invalid groups are rejected (lenient one returns empty)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: all-invalid groups are rejected (lenient one returns empty)")
# Lenient measured behaviour: "!!!!" / "%%" / "...." -> "" — a caller
# cannot distinguish that from a legitimately empty payload.
for v in ["!!!!", "%%", "...."]:
    assert_equal(base64url_decode(v), "")          # lenient: no signal
    assert_equal(base64url_decode_strict(v).is_ok(), false)
```

</details>

#### REPRODUCING: mixed valid/invalid is rejected, not partially decoded

- REPRODUCING: mixed valid/invalid is rejected, not partially decoded


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: mixed valid/invalid is rejected, not partially decoded")
# Lenient measured behaviour: the invalid symbol is DROPPED and the
# valid remainder decoded, so a malformed segment looks well-formed.
assert_equal(base64url_decode("ab*d").len(), 2)    # lenient
assert_equal(base64url_decode_strict("ab*d").is_ok(), false)

assert_equal(base64url_decode("a b c").len(), 2)   # lenient
assert_equal(base64url_decode_strict("a b c").is_ok(), false)
```

</details>

#### REPRODUCING: standard-alphabet '+' and '/' are rejected

- REPRODUCING: standard-alphabet '+' and '/' are rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: standard-alphabet '+' and '/' are rejected")
# Lenient measured behaviour: "a+b/c" -> 3 chars. '+' and '/' are the
# STANDARD alphabet's chars 62/63; base64url uses '-' and '_'.
assert_equal(base64url_decode("a+b/c").len(), 3)   # lenient
assert_equal(base64url_decode_strict("a+b/c").is_ok(), false)
assert_equal(base64url_decode_strict("a+bc").is_ok(), false)
assert_equal(base64url_decode_strict("ab/c").is_ok(), false)
```

</details>

#### DEFECT CLASS: every valid unpadded base64url of length 0..99 round-trips

- DEFECT CLASS: every valid unpadded base64url of length 0..99 round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: every valid unpadded base64url of length 0..99 round-trips")
# The strict decoder must ACCEPT all well-formed input — a rejector
# that rejects too much is the same defect with the sign flipped.
# Payload lengths 0..99 cover every mod-3 residue, hence every valid
# encoded-length residue (0, 2, 3 mod 4), at many sizes.
var accepted = 0
var k = 0
while k < 100:
    var payload = ""
    var j = 0
    while j < k:
        payload = payload + "abcdefghijklmnopqrstuvwxyz0123456789".char_at(j % 36)
        j = j + 1
    val enc = base64url_encode(payload)
    assert_true(enc.bytes().len() % 4 != 1)
    val r = base64url_decode_strict(enc)
    assert_equal(r.is_ok(), true)
    assert_equal(r.unwrap(), payload)
    # Same bytes as the lenient decoder on valid input: strict changes
    # only the invalid path, never the well-formed one.
    assert_equal(r.unwrap(), base64url_decode(enc))
    accepted = accepted + 1
    k = k + 1
assert_equal(accepted, 100)
```

</details>

#### DEFECT CLASS: the empty string is VALID base64url and decodes to empty

- DEFECT CLASS: the empty string is VALID base64url and decodes to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: the empty string is VALID base64url and decodes to empty")
# Documented decision: zero bytes encode to zero characters, residue
# 0 mod 4, so "" is well-formed and must be Ok(""), NOT an error.
val r = base64url_decode_strict("")
assert_equal(r.is_ok(), true)
assert_equal(r.unwrap(), "")
```

</details>

#### DEFECT CLASS: length residue 1 mod 4 is impossible and is rejected

- DEFECT CLASS: length residue 1 mod 4 is impossible and is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: length residue 1 mod 4 is impossible and is rejected")
# No byte sequence encodes to a length of 1 mod 4, so such a tail is
# always truncation — even when every character is in the alphabet.
for v in ["a", "abcde", "abcdefffi"]:
    assert_true(v.bytes().len() % 4 == 1)
    assert_equal(base64url_decode_strict(v).is_ok(), false)
```

</details>

#### DEFECT CLASS: padding, whitespace and control bytes are rejected

- DEFECT CLASS: padding, whitespace and control bytes are rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: padding, whitespace and control bytes are rejected")
# '=' is valid in PADDED base64 but not in the unpadded url form;
# whitespace is skipped by the lenient decoder and must not be here.
for v in ["ab==", "abc=", "ab\tc", "ab\nc", "ab c", "a\rbc"]:
    assert_equal(base64url_decode_strict(v).is_ok(), false)
```

</details>

#### DEFECT CLASS: a single invalid byte anywhere in a long valid string is caught

- DEFECT CLASS: a single invalid byte anywhere in a long valid string is caught


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: a single invalid byte anywhere in a long valid string is caught")
# Guards against a validator that only inspects a prefix or a tail.
val good = base64url_encode("the quick brown fox jumps over the lazy dog")
assert_equal(base64url_decode_strict(good).is_ok(), true)
val n = good.bytes().len()
for pos in [0, 1, n / 2, n - 1]:
    val broken = good.substring(0, pos) + "*" + good.substring(pos + 1, n)
    assert_equal(broken.bytes().len(), n)
    assert_equal(base64url_decode_strict(broken).is_ok(), false)
```

</details>

#### DEFECT CLASS: '-' and '_' (the url-safe chars 62/63) are ACCEPTED

- DEFECT CLASS: '-' and '_' (the url-safe chars 62/63) are ACCEPTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: '-' and '_' (the url-safe chars 62/63) are ACCEPTED")
# The mirror of the '+'/'/' rejection above: rejecting these instead
# would break every real JWT.
val r = base64url_decode_strict("-_-_")
assert_equal(r.is_ok(), true)
assert_equal(r.unwrap(), base64url_decode("-_-_"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base64url_decode_strict — rejects out-of-alphabet input (RFC 4648 s3.3).
- base64url_decode_strict — rejects out-of-alphabet input (RFC 4648 s3.3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `bd0a0bde0f76942f90625f6fc171f752386379ae62a37d6b8449137bf171d9b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd0a0bde0f76942f90625f6fc171f752386379ae62a37d6b8449137bf171d9b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd0a0bde0f76942f90625f6fc171f752386379ae62a37d6b8449137bf171d9b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: the strict decoder under test is really loaded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPRODUCING: all-invalid groups are rejected (lenient one returns empty)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_decode_strict_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPRODUCING: mixed valid/invalid is rejected, not partially decoded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
