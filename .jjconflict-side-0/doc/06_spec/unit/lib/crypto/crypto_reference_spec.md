# Crypto Reference Specification

> Tests covering constant_time_compare, legacy hash reference vectors, PBKDF2 reference vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crypto Reference Specification

## Scenarios

### constant_time_compare

#### matches equality semantics for same length values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches equality semantics for same length values
   - Expected: constant_time_compare("abcdef", "abcdef") is true
   - Expected: constant_time_compare("abcdef", "abcdeg") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches equality semantics for same length values")
expect(constant_time_compare("abcdef", "abcdef")).to_equal(true)
expect(constant_time_compare("abcdef", "abcdeg")).to_equal(false)
```

</details>

#### rejects different length values

- rejects different length values
   - Expected: constant_time_compare("abcdef", "abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects different length values")
expect(constant_time_compare("abcdef", "abc")).to_equal(false)
```

</details>

### legacy hash reference vectors

#### matches SHA-1 known-answer vectors

- matches SHA-1 known-answer vectors
   - Expected: sha1_hex("") equals `da39a3ee5e6b4b0d3255bfef95601890afd80709`
   - Expected: sha1_hex("abc") equals `a9993e364706816aba3e25717850c26c9cd0d89d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches SHA-1 known-answer vectors")
expect(sha1_hex("")).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_hex("abc")).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

#### matches MD5 known-answer vectors

- matches MD5 known-answer vectors
   - Expected: md5_hex("") equals `d41d8cd98f00b204e9800998ecf8427e`
   - Expected: md5_hex("abc") equals `900150983cd24fb0d6963f7d28e17f72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches MD5 known-answer vectors")
expect(md5_hex("")).to_equal("d41d8cd98f00b204e9800998ecf8427e")
expect(md5_hex("abc")).to_equal("900150983cd24fb0d6963f7d28e17f72")
```

</details>

### PBKDF2 reference vectors

#### matches PBKDF2-HMAC-SHA256 RFC 6070 style vector

- matches PBKDF2-HMAC-SHA256 RFC 6070 style vector
   - Expected: bytes_to_hex(derived) equals `120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches PBKDF2-HMAC-SHA256 RFC 6070 style vector")
val derived = pbkdf2_sha256("password", "salt", 1)
expect(bytes_to_hex(derived)).to_equal("120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b")
```

</details>

#### matches PBKDF2-HMAC-SHA512 reference vector

- matches PBKDF2-HMAC-SHA512 reference vector
   - Expected: bytes_to_hex(derived) equals `867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches PBKDF2-HMAC-SHA512 reference vector")
val derived = pbkdf2_sha512("password", "salt", 1)
expect(bytes_to_hex(derived)).to_equal("867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce")
```

</details>

#### uses SHA-256 as the default algorithm

- uses SHA-256 as the default algorithm
   - Expected: bytes_to_hex(fallback) equals `bytes_to_hex(explicit)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses SHA-256 as the default algorithm")
val explicit = pbkdf2_sha256("password", "salt", 1)
val fallback = pbkdf2_with_algorithm("password", "salt", 1, "unknown")
expect(bytes_to_hex(fallback)).to_equal(bytes_to_hex(explicit))
expect(get_recommended_pbkdf2_iterations()).to_be_greater_than(99999)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/crypto_reference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering constant_time_compare, legacy hash reference vectors, PBKDF2 reference vectors.
- constant_time_compare
- legacy hash reference vectors
- PBKDF2 reference vectors

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

- Canonical SPipe generation for source `0695ca14e713f0556c0f5f0d44081e0bc812b2b0c1646fbe8ee8674ff7f1e571`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0695ca14e713f0556c0f5f0d44081e0bc812b2b0c1646fbe8ee8674ff7f1e571`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0695ca14e713f0556c0f5f0d44081e0bc812b2b0c1646fbe8ee8674ff7f1e571`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/crypto_reference_spec.spl
mirror: doc/06_spec/unit/lib/crypto/crypto_reference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/crypto_reference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/crypto_reference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/crypto_reference_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches equality semantics for same length values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/crypto_reference_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects different length values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/crypto_reference_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches SHA-1 known-answer vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
