# Sha2 Nist Vectors Specification

> Tests covering SHA-256 NIST FIPS 180-4 test vectors, SHA-512 NIST FIPS 180-4 test vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha2 Nist Vectors Specification

## Scenarios

### SHA-256 NIST FIPS 180-4 test vectors

#### FIPS 180-4 §B.0 empty string digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FIPS 180-4 §B.0 empty string digest
   - Expected: sha256_text("") equals `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §B.0 empty string digest")
# Expected: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
expect(sha256_text("")).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### FIPS 180-4 §B.1 'abc' (canary) digest

- FIPS 180-4 §B.1 'abc' (canary) digest
   - Expected: sha256_text("abc") equals `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §B.1 'abc' (canary) digest")
# Expected: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
expect(sha256_text("abc")).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### FIPS 180-4 §B.2 56-byte string digest

- FIPS 180-4 §B.2 56-byte string digest
   - Expected: sha256_text("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") equals `248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §B.2 56-byte string digest")
# Input: "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
# Expected: 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
expect(sha256_text("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")).to_equal("248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
```

</details>

#### multi-block: 1024 bytes of 0x61 ('a') — 16 SHA-256 blocks

- multi-block: 1024 bytes of 0x61 ('a') — 16 SHA-256 blocks
   - Expected: bytes_to_hex(sha256_bytes(input)) equals `2edc986847e209b4016e141a6dc8716d3207350f416969382d431539bf292e4a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-block: 1024 bytes of 0x61 ('a') — 16 SHA-256 blocks")
# DEVIATION: FIPS §B.3 specifies 1M 'a' bytes (cdc76e5c...); replaced with
# 1024 bytes to stay within interpreter timeout. Multi-block boundary covered.
# Reference: python3 => 2edc986847e209b4016e141a6dc8716d3207350f416969382d431539bf292e4a
val input = _make_1024_a()
expect(bytes_to_hex(sha256_bytes(input))).to_equal("2edc986847e209b4016e141a6dc8716d3207350f416969382d431539bf292e4a")
```

</details>

### SHA-512 NIST FIPS 180-4 test vectors

#### FIPS 180-4 §C.0 empty string digest

- FIPS 180-4 §C.0 empty string digest
   - Expected: sha512_text("") equals `cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §C.0 empty string digest")
# Expected: cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce
#           47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e
expect(sha512_text("")).to_equal("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
```

</details>

#### FIPS 180-4 §C.1 'abc' (canary) digest

- FIPS 180-4 §C.1 'abc' (canary) digest
   - Expected: sha512_text("abc") equals `ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §C.1 'abc' (canary) digest")
# Expected: ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
#           2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
expect(sha512_text("abc")).to_equal("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
```

</details>

#### FIPS 180-4 §C.2 112-byte string digest

- FIPS 180-4 §C.2 112-byte string digest
   - Expected: sha512_text("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") equals `8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §C.2 112-byte string digest")
# Input: "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn
#         hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
# Expected: 8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018
#           501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909
expect(sha512_text("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")).to_equal("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
```

</details>

#### multi-block: 1024 bytes of 0x61 ('a') — 8 SHA-512 blocks

- multi-block: 1024 bytes of 0x61 ('a') — 8 SHA-512 blocks
   - Expected: bytes_to_hex(sha512_bytes(input)) equals `74b22492e3b9a86a9c93c23a69f821ebafa429302c1f4054b4bc37356a4bae056d9ccbc6f2409... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-block: 1024 bytes of 0x61 ('a') — 8 SHA-512 blocks")
# DEVIATION: FIPS §C.3 specifies 1M 'a' bytes; reduced to 1024.
# Reference: python3 => 74b22492e3b9a86a9c93c23a69f821ebafa429302c1f4054b4bc37356a4bae05
#                        6d9ccbc6f24093a25704faaa72bd21a5f337ca9ec92f32369d24e6b9fae954d8
val input = _make_1024_a()
expect(bytes_to_hex(sha512_bytes(input))).to_equal("74b22492e3b9a86a9c93c23a69f821ebafa429302c1f4054b4bc37356a4bae056d9ccbc6f24093a25704faaa72bd21a5f337ca9ec92f32369d24e6b9fae954d8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-256 NIST FIPS 180-4 test vectors, SHA-512 NIST FIPS 180-4 test vectors.
- SHA-256 NIST FIPS 180-4 test vectors
- SHA-512 NIST FIPS 180-4 test vectors

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `683b883ddfe7b3a44f3343bff581592bc9063156500c62b67c4caac6b24b170b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `683b883ddfe7b3a44f3343bff581592bc9063156500c62b67c4caac6b24b170b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `683b883ddfe7b3a44f3343bff581592bc9063156500c62b67c4caac6b24b170b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/sha2_nist_vectors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/sha2_nist_vectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/sha2_nist_vectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 180-4 §B.0 empty string digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 180-4 §B.1 'abc' (canary) digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 180-4 §B.2 56-byte string digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
