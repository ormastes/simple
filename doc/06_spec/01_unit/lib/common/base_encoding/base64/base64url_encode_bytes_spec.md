# Base64url Encode Bytes Specification

> Tests covering base64url_encode_bytes — binary-safe encode agrees with the deleted locals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64url Encode Bytes Specification

## Scenarios

### base64url_encode_bytes — binary-safe encode agrees with the deleted locals

#### POSITIVE CONTROL: the std encoder under test is really loaded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: the std encoder under test is really loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: the std encoder under test is really loaded")
# If the import silently resolved to nothing, an equivalence assertion
# comparing two empty/sentinel values could pass for the wrong reason.
# This demands an exact non-trivial encoding of a known input, which no
# absent or sentinel value produces.
assert_equal(base64url_encode_bytes("Simple".bytes()), "U2ltcGxl")
assert_equal(base64url_encode_i64_bytes([83, 105, 109, 112, 108, 101]), "U2ltcGxl")
# ...and the ORACLE is loaded too, so a green run cannot mean the
# comparison function itself was missing.
assert_equal(oracle_encode([83, 105, 109, 112, 108, 101]), "U2ltcGxl")
```

</details>

#### EQUIVALENCE: agrees with the oracle on a full 32-byte HMAC-SHA256 digest

- EQUIVALENCE: agrees with the oracle on a full 32-byte HMAC-SHA256 digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("EQUIVALENCE: agrees with the oracle on a full 32-byte HMAC-SHA256 digest")
# This is the exact call shape the JWT signing path uses: 32 bytes,
# 32 % 3 == 2, so the final group is a 2-byte remainder — the case
# where a padding/length mistake would show up.
val d = digest_corpus()
assert_equal(base64url_encode_i64_bytes(d), oracle_encode(d))
assert_equal(base64url_encode_bytes(to_u8(d)), oracle_encode(d))
assert_equal(base64url_encode_i64_bytes(d).len(), 43)   # ceil(32*4/3), unpadded
```

</details>

#### EQUIVALENCE: agrees on the boundary bytes a text corpus cannot reach

- EQUIVALENCE: agrees on the boundary bytes a text corpus cannot reach


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("EQUIVALENCE: agrees on the boundary bytes a text corpus cannot reach")
# One byte at a time: 0x00, 0x7f, 0x80, 0xFF. Each is a single-byte
# input, i.e. the 1-byte-remainder group (2 output chars, no padding).
for b in [0, 127, 128, 255]:
    assert_equal(base64url_encode_i64_bytes([b]), oracle_encode([b]))
    assert_equal(base64url_encode_i64_bytes([b]).len(), 2)
```

</details>

#### EQUIVALENCE: agrees on every input length mod 3 (remainder handling)

- EQUIVALENCE: agrees on every input length mod 3 (remainder handling)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("EQUIVALENCE: agrees on every input length mod 3 (remainder handling)")
# Lengths 0..8 cover all three residues more than once. A padding bug
# is a residue bug, so this is where '=' leakage would surface.
val d = digest_corpus()
var n = 0
while n <= 8:
    var slice: [i64] = []
    var i = 0
    while i < n:
        slice = slice.push(d[i])
        i = i + 1
    assert_equal(base64url_encode_i64_bytes(slice), oracle_encode(slice))
    n = n + 1
```

</details>

#### EQUIVALENCE: emits no padding and no standard-alphabet characters

- EQUIVALENCE: emits no padding and no standard-alphabet characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("EQUIVALENCE: emits no padding and no standard-alphabet characters")
# RFC 4648 section 5: '-' and '_' replace '+' and '/', and '=' is absent.
val out = base64url_encode_i64_bytes(digest_corpus())
assert_equal(out.index_of("="), -1)
assert_equal(out.index_of("+"), -1)
assert_equal(out.index_of("/"), -1)
```

</details>

#### EQUIVALENCE: byte-identical to base64url_encode for valid-text input

- EQUIVALENCE: byte-identical to base64url_encode for valid-text input


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("EQUIVALENCE: byte-identical to base64url_encode for valid-text input")
# The consolidation must not fork the two encoders. For any input that
# happens to be valid text, the byte-taking and text-taking functions
# must agree — they share the fused `_base64url_encode_raw`,
# so this holds by construction; this example pins that.
for s in ["", "f", "fo", "foo", "foob", "fooba", "foobar",
          "Simple", "any carnal pleasure?", "~!@#$%^&*()_+"]:
    assert_equal(base64url_encode_bytes(s.bytes()), base64url_encode(s))
```

</details>

#### ROUND-TRIP: encode_bytes then base64url_decode_strict returns the input

- ROUND-TRIP: encode_bytes then base64url_decode_strict returns the input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ROUND-TRIP: encode_bytes then base64url_decode_strict returns the input")
# Strict decode returns Result<text, _>, so the round-trip is asserted
# over text-safe inputs, where text and bytes are the same information.
for s in ["f", "fo", "foo", "foob", "fooba", "foobar", "Simple"]:
    val r = base64url_decode_strict(base64url_encode_bytes(s.bytes()))
    assert_equal(r.is_ok(), true)
    assert_equal(r.unwrap(), s)
```

</details>

#### ROUND-TRIP: arbitrary-binary output is accepted by the strict decoder

- ROUND-TRIP: arbitrary-binary output is accepted by the strict decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ROUND-TRIP: arbitrary-binary output is accepted by the strict decoder")
# The digest's own round-trip cannot be asserted through the text-typed
# decoder without loss (that lossiness is the reason this byte-taking
# encoder exists at all). What IS assertable, and what the signing path
# actually depends on, is that the encoding is well-formed unpadded
# base64url — i.e. the strict decoder accepts it rather than rejecting
# it as an out-of-alphabet or residue-1 string.
val out = base64url_encode_i64_bytes(digest_corpus())
assert_equal(base64url_decode_strict(out).is_ok(), true)
for b in [0, 127, 128, 255]:
    assert_true(base64url_decode_strict(base64url_encode_i64_bytes([b, b, b])).is_ok())
```

</details>

#### DEFECT CLASS: an out-of-range [i64] element is masked, not leaked

- DEFECT CLASS: an out-of-range [i64] element is masked, not leaked


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: an out-of-range [i64] element is masked, not leaked")
# std.crypto represents bytes as [i64]. An element outside 0..255 must
# not corrupt neighbouring output sextets; it is masked to its low 8
# bits, matching what the deleted locals did implicitly via % 64.
assert_equal(base64url_encode_i64_bytes([256, 257, 258]),
             base64url_encode_i64_bytes([0, 1, 2]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base64url_encode_bytes — binary-safe encode agrees with the deleted locals.
- base64url_encode_bytes — binary-safe encode agrees with the deleted locals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `4abc48ea83a48ae27804315cef4869877b1aeb89df7aca2ce04aec4e17ff1e9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4abc48ea83a48ae27804315cef4869877b1aeb89df7aca2ce04aec4e17ff1e9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4abc48ea83a48ae27804315cef4869877b1aeb89df7aca2ce04aec4e17ff1e9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: the std encoder under test is really loaded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EQUIVALENCE: agrees with the oracle on a full 32-byte HMAC-SHA256 digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base64/base64url_encode_bytes_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EQUIVALENCE: agrees on the boundary bytes a text corpus cannot reach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
