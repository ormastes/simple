# Sha256 X4 Specification

> Tests covering sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes, sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes, sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes, sha256_x4 lane independence — 4 different inputs, sha256_x4 regression vs scalar sha256_bytes, sha256_x4 pre-padded single block — boundary test, sha256_x4 regression — diverse inputs match scalar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 X4 Specification

## Scenarios

### sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes

#### all 4 lanes of empty input produce e3b0c442...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all 4 lanes of empty input produce e3b0c442...
   - Expected: sha256_digest_to_hex(d0) equals `expected`
   - Expected: sha256_digest_to_hex(d1) equals `expected`
   - Expected: sha256_digest_to_hex(d2) equals `expected`
   - Expected: sha256_digest_to_hex(d3) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of empty input produce e3b0c442...")
val empty: list = []
val result = sha256_x4_message(empty, empty, empty, empty)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "e3b0c44298fc1c149afbf4c8996fb924" + "27ae41e4649b934ca495991b7852b855"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes

#### all 4 lanes of 'abc' produce ba7816bf...

- all 4 lanes of 'abc' produce ba7816bf...
   - Expected: sha256_digest_to_hex(d0) equals `expected`
   - Expected: sha256_digest_to_hex(d1) equals `expected`
   - Expected: sha256_digest_to_hex(d2) equals `expected`
   - Expected: sha256_digest_to_hex(d3) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of 'abc' produce ba7816bf...")
val abc = [0x61, 0x62, 0x63]
val result = sha256_x4_message(abc, abc, abc, abc)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "ba7816bf8f01cfea414140de5dae2223" + "b00361a396177a9cb410ff61f20015ad"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes

#### all 4 lanes of 56-byte NIST input produce 248d6a61...

- all 4 lanes of 56-byte NIST input produce 248d6a61...
   - Expected: sha256_digest_to_hex(d0) equals `expected`
   - Expected: sha256_digest_to_hex(d1) equals `expected`
   - Expected: sha256_digest_to_hex(d2) equals `expected`
   - Expected: sha256_digest_to_hex(d3) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of 56-byte NIST input produce 248d6a61...")
val m = _nist_56_byte()
val result = sha256_x4_message(m, m, m, m)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "248d6a61d20638b8e5c026930c3e6039" + "a33ce45964ff2167f6ecedd419db06c1"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 lane independence — 4 different inputs

#### 4 distinct inputs produce 4 distinct digests

- 4 distinct inputs produce 4 distinct digests
   - Expected: d0 != d1 is true
   - Expected: d0 != d2 is true
   - Expected: d0 != d3 is true
   - Expected: d1 != d2 is true
   - Expected: d1 != d3 is true
   - Expected: d2 != d3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4 distinct inputs produce 4 distinct digests")
val m0: list = []                         # empty
val m1 = [0x61, 0x62, 0x63]              # "abc"
val m2 = [0x61]                           # "a"
val m3 = [0x62, 0x63]                     # "bc"
val result = sha256_x4_message(m0, m1, m2, m3)
val d0 = sha256_digest_to_hex(result.get(0))
val d1 = sha256_digest_to_hex(result.get(1))
val d2 = sha256_digest_to_hex(result.get(2))
val d3 = sha256_digest_to_hex(result.get(3))
# All four digests must differ (lane independence)
expect(d0 != d1).to_equal(true)
expect(d0 != d2).to_equal(true)
expect(d0 != d3).to_equal(true)
expect(d1 != d2).to_equal(true)
expect(d1 != d3).to_equal(true)
expect(d2 != d3).to_equal(true)
```

</details>

### sha256_x4 regression vs scalar sha256_bytes

#### x4 lane results match sha256_bytes scalar for same 4 inputs

- x4 lane results match sha256_bytes scalar for same 4 inputs
   - Expected: _list_eq(result.get(0), s0) is true
   - Expected: _list_eq(result.get(1), s1) is true
   - Expected: _list_eq(result.get(2), s2) is true
   - Expected: _list_eq(result.get(3), s3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane results match sha256_bytes scalar for same 4 inputs")
val m0: list = []
val m1 = [0x61, 0x62, 0x63]
val m2 = [0x61]
val m3 = [0x62, 0x63]
val result = sha256_x4_message(m0, m1, m2, m3)
val s0 = sha256_bytes(m0)
val s1 = sha256_bytes(m1)
val s2 = sha256_bytes(m2)
val s3 = sha256_bytes(m3)
expect(_list_eq(result.get(0), s0)).to_equal(true)
expect(_list_eq(result.get(1), s1)).to_equal(true)
expect(_list_eq(result.get(2), s2)).to_equal(true)
expect(_list_eq(result.get(3), s3)).to_equal(true)
```

</details>

### sha256_x4 pre-padded single block — boundary test

#### sha256_x4 of manually padded 'abc' block matches sha256_bytes

- sha256_x4 of manually padded 'abc' block matches sha256_bytes
   - Expected: _list_eq(d0, expected) is true
   - Expected: _list_eq(d1, expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sha256_x4 of manually padded 'abc' block matches sha256_bytes")
# SHA-256 pad of "abc" (3 bytes) -> exactly 64 bytes
# abc = [0x61, 0x62, 0x63], then 0x80, zeros to 56 bytes, then 64-bit big-endian 24
val abc = [0x61, 0x62, 0x63]
val padded_abc = _sha256_pad_for_test(abc)
val result = sha256_x4(padded_abc, padded_abc, padded_abc, padded_abc)
val d0 = result.get(0)
val d1 = result.get(1)
val expected = sha256_bytes(abc)
expect(_list_eq(d0, expected)).to_equal(true)
expect(_list_eq(d1, expected)).to_equal(true)
```

</details>

### sha256_x4 regression — diverse inputs match scalar

#### zero-block, 'def', 'ghi', 10-zero-bytes all match scalar

- zero-block, 'def', 'ghi', 10-zero-bytes all match scalar
   - Expected: _list_eq(result.get(0), expected0) is true
   - Expected: _list_eq(result.get(1), expected1) is true
   - Expected: _list_eq(result.get(2), expected2) is true
   - Expected: _list_eq(result.get(3), expected3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-block, 'def', 'ghi', 10-zero-bytes all match scalar")
val zero_block = _make_repeat(0, 10)
val m1 = [0x64, 0x65, 0x66]   # "def"
val m2 = [0x67, 0x68, 0x69]   # "ghi"
val m3 = [0x61, 0x62, 0x63, 0x64]  # "abcd"
val result = sha256_x4_message(zero_block, m1, m2, m3)
val expected0 = sha256_bytes(zero_block)
val expected1 = sha256_bytes(m1)
val expected2 = sha256_bytes(m2)
val expected3 = sha256_bytes(m3)
expect(_list_eq(result.get(0), expected0)).to_equal(true)
expect(_list_eq(result.get(1), expected1)).to_equal(true)
expect(_list_eq(result.get(2), expected2)).to_equal(true)
expect(_list_eq(result.get(3), expected3)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/sha256_x4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes, sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes, sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes, sha256_x4 lane independence — 4 different inputs, sha256_x4 regression vs scalar sha256_bytes, sha256_x4 pre-padded single block — boundary test, sha256_x4 regression — diverse inputs match scalar.
- sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes
- sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes
- sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes
- sha256_x4 lane independence — 4 different inputs
- sha256_x4 regression vs scalar sha256_bytes
- sha256_x4 pre-padded single block — boundary test
- sha256_x4 regression — diverse inputs match scalar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d178fada2a7dcc54dec5437283f5580feff49f08cef1378655429761f235a351`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d178fada2a7dcc54dec5437283f5580feff49f08cef1378655429761f235a351`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d178fada2a7dcc54dec5437283f5580feff49f08cef1378655429761f235a351`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/sha256_x4_spec.spl
mirror: doc/06_spec/unit/lib/crypto/sha256_x4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/sha256_x4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/sha256_x4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/sha256_x4_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of empty input produce e3b0c442...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha256_x4_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of 'abc' produce ba7816bf...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha256_x4_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of 56-byte NIST input produce 248d6a61...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
