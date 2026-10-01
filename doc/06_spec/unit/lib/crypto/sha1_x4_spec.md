# Sha1 X4 Specification

> Tests covering sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes, sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes, sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes, sha1_x4 lane independence — 4 different inputs, sha1_x4 regression vs scalar sha1_bytes, sha1_x4 zero-block first lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha1 X4 Specification

## Scenarios

### sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes

#### all 4 lanes of empty input produce da39a3ee...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all 4 lanes of empty input produce da39a3ee...
   - Expected: sha1_digest_to_hex(d0) equals `da39a3ee5e6b4b0d3255bfef95601890afd80709`
   - Expected: sha1_digest_to_hex(d1) equals `da39a3ee5e6b4b0d3255bfef95601890afd80709`
   - Expected: sha1_digest_to_hex(d2) equals `da39a3ee5e6b4b0d3255bfef95601890afd80709`
   - Expected: sha1_digest_to_hex(d3) equals `da39a3ee5e6b4b0d3255bfef95601890afd80709`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of empty input produce da39a3ee...")
val empty: list = []
val result = sha1_x4_message(empty, empty, empty, empty)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d1)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d2)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d3)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
```

</details>

### sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes

#### all 4 lanes of 'abc' produce a9993e36...

- all 4 lanes of 'abc' produce a9993e36...
   - Expected: sha1_digest_to_hex(d0) equals `a9993e364706816aba3e25717850c26c9cd0d89d`
   - Expected: sha1_digest_to_hex(d1) equals `a9993e364706816aba3e25717850c26c9cd0d89d`
   - Expected: sha1_digest_to_hex(d2) equals `a9993e364706816aba3e25717850c26c9cd0d89d`
   - Expected: sha1_digest_to_hex(d3) equals `a9993e364706816aba3e25717850c26c9cd0d89d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of 'abc' produce a9993e36...")
val abc = [0x61, 0x62, 0x63]
val result = sha1_x4_message(abc, abc, abc, abc)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d1)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d2)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d3)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

### sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes

#### all 4 lanes of 56-byte NIST input produce 84983e44...

- all 4 lanes of 56-byte NIST input produce 84983e44...
   - Expected: sha1_digest_to_hex(d0) equals `84983e441c3bd26ebaae4aa1f95129e5e54670f1`
   - Expected: sha1_digest_to_hex(d1) equals `84983e441c3bd26ebaae4aa1f95129e5e54670f1`
   - Expected: sha1_digest_to_hex(d2) equals `84983e441c3bd26ebaae4aa1f95129e5e54670f1`
   - Expected: sha1_digest_to_hex(d3) equals `84983e441c3bd26ebaae4aa1f95129e5e54670f1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lanes of 56-byte NIST input produce 84983e44...")
val m = _nist_56_byte()
val result = sha1_x4_message(m, m, m, m)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d1)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d2)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d3)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
```

</details>

### sha1_x4 lane independence — 4 different inputs

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
val result = sha1_x4_message(m0, m1, m2, m3)
val d0 = sha1_digest_to_hex(result.get(0))
val d1 = sha1_digest_to_hex(result.get(1))
val d2 = sha1_digest_to_hex(result.get(2))
val d3 = sha1_digest_to_hex(result.get(3))
# All four digests must differ (lane independence)
expect(d0 != d1).to_equal(true)
expect(d0 != d2).to_equal(true)
expect(d0 != d3).to_equal(true)
expect(d1 != d2).to_equal(true)
expect(d1 != d3).to_equal(true)
expect(d2 != d3).to_equal(true)
```

</details>

### sha1_x4 regression vs scalar sha1_bytes

#### x4 lane results match sha1_bytes scalar for same 4 inputs

- x4 lane results match sha1_bytes scalar for same 4 inputs
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
step("x4 lane results match sha1_bytes scalar for same 4 inputs")
val m0: list = []
val m1 = [0x61, 0x62, 0x63]
val m2 = [0x61]
val m3 = [0x62, 0x63]
val result = sha1_x4_message(m0, m1, m2, m3)
val s0 = sha1_bytes(m0)
val s1 = sha1_bytes(m1)
val s2 = sha1_bytes(m2)
val s3 = sha1_bytes(m3)
expect(_list_eq(result.get(0), s0)).to_equal(true)
expect(_list_eq(result.get(1), s1)).to_equal(true)
expect(_list_eq(result.get(2), s2)).to_equal(true)
expect(_list_eq(result.get(3), s3)).to_equal(true)
```

</details>

### sha1_x4 zero-block first lane

#### lane 0 matches sha1_bytes of zero-block; others match scalar independently

- lane 0 matches sha1_bytes of zero-block; others match scalar independently
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
step("lane 0 matches sha1_bytes of zero-block; others match scalar independently")
val zero_block = _make_repeat(0, 10)   # 10 zero bytes
val m1 = [0x61, 0x62, 0x63]            # "abc"
val m2 = [0x64, 0x65, 0x66]            # "def"
val m3 = [0x67, 0x68, 0x69]            # "ghi"
val result = sha1_x4_message(zero_block, m1, m2, m3)
val expected0 = sha1_bytes(zero_block)
val expected1 = sha1_bytes(m1)
val expected2 = sha1_bytes(m2)
val expected3 = sha1_bytes(m3)
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
| Source | `test/unit/lib/crypto/sha1_x4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes, sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes, sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes, sha1_x4 lane independence — 4 different inputs, sha1_x4 regression vs scalar sha1_bytes, sha1_x4 zero-block first lane.
- sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes
- sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes
- sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes
- sha1_x4 lane independence — 4 different inputs
- sha1_x4 regression vs scalar sha1_bytes
- sha1_x4 zero-block first lane

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ebd5b4d1ad76885980172178c21aa4810adda3d52ec6d1cdbd779cc20a55d4f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebd5b4d1ad76885980172178c21aa4810adda3d52ec6d1cdbd779cc20a55d4f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebd5b4d1ad76885980172178c21aa4810adda3d52ec6d1cdbd779cc20a55d4f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/sha1_x4_spec.spl
mirror: doc/06_spec/unit/lib/crypto/sha1_x4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/sha1_x4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/sha1_x4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/sha1_x4_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of empty input produce da39a3ee...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha1_x4_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of 'abc' produce a9993e36...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha1_x4_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all 4 lanes of 56-byte NIST input produce 84983e44...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
