# Blake2 Rfc7693 Kat Specification

> Tests covering BLAKE2b RFC 7693 Appendix A test vectors, BLAKE2s RFC 7693 Appendix B test vectors, BLAKE2 keyed-mode KATs (blake2-kat.json).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2 Rfc7693 Kat Specification

## Scenarios

### BLAKE2b RFC 7693 Appendix A test vectors

#### Appendix A 'abc' unkeyed digest (64 bytes)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Appendix A 'abc' unkeyed digest (64 bytes)
   - Expected: _bytes_to_hex(digest) equals `ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab7... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Appendix A 'abc' unkeyed digest (64 bytes)")
# Expected: ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1
#           7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
val msg = _abc_bytes()
val key = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
```

</details>

#### multi-block: 128 bytes of 'a' unkeyed (1 full block, 64-byte digest)

- multi-block: 128 bytes of 'a' unkeyed (1 full block, 64-byte digest)
   - Expected: _bytes_to_hex(digest) equals `fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047e... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-block: 128 bytes of 'a' unkeyed (1 full block, 64-byte digest)")
# 128 bytes = exactly one BLAKE2b block; exercises the all-block-is-final path.
# Reference (Python hashlib.blake2b):
#   fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a7
#   6b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b
val msg = _repeat_bytes(0x61, 128)
val key = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b")
```

</details>

### BLAKE2s RFC 7693 Appendix B test vectors

#### Appendix B 'abc' unkeyed digest (32 bytes)

- Appendix B 'abc' unkeyed digest (32 bytes)
   - Expected: _bytes_to_hex(digest) equals `508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Appendix B 'abc' unkeyed digest (32 bytes)")
# Expected: 508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
val msg = _abc_bytes()
val key = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### multi-block: 64 bytes of 'a' unkeyed (1 full block, 32-byte digest)

- multi-block: 64 bytes of 'a' unkeyed (1 full block, 32-byte digest)
   - Expected: _bytes_to_hex(digest) equals `651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-block: 64 bytes of 'a' unkeyed (1 full block, 32-byte digest)")
# Reference (Python hashlib.blake2s):
#   651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
val msg = _repeat_bytes(0x61, 64)
val key = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252")
```

</details>

### BLAKE2 keyed-mode KATs (blake2-kat.json)

#### BLAKE2b key=00..3f in='' out=64 (blake2-kat.json kk=64 in='')

- BLAKE2b key=00..3f in='' out=64 (blake2-kat.json kk=64 in='')
   - Expected: _bytes_to_hex(digest) equals `10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4e... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLAKE2b key=00..3f in='' out=64 (blake2-kat.json kk=64 in='')")
# Expected: 10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786
#           b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568
val key = _range_bytes(64)
val msg = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568")
```

</details>

#### BLAKE2s key=00..1f in='' out=32 (blake2-kat.json kk=32 in='')

- BLAKE2s key=00..1f in='' out=32 (blake2-kat.json kk=32 in='')
   - Expected: _bytes_to_hex(digest) equals `48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLAKE2s key=00..1f in='' out=32 (blake2-kat.json kk=32 in='')")
# Expected: 48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49
val key = _range_bytes(32)
val msg = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49")
```

</details>

#### BLAKE2b key=00..07 in='Hi There' out=64

- BLAKE2b key=00..07 in='Hi There' out=64
   - Expected: _bytes_to_hex(digest) equals `0f3623fb9296d25e4ebf6d11139e105a6265ad20bb38060e393fe43c9643718d565d8c82d0892... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLAKE2b key=00..07 in='Hi There' out=64")
# Reference (Python hashlib.blake2b, key=bytes(range(8))):
#   0f3623fb9296d25e4ebf6d11139e105a6265ad20bb38060e393fe43c9643718d
#   565d8c82d089265102171de74ff8dcdff7cd299f06d69d467a9be55c5d26cc95
val key = _range_bytes(8)
val msg = _hi_there_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("0f3623fb9296d25e4ebf6d11139e105a6265ad20bb38060e393fe43c9643718d565d8c82d089265102171de74ff8dcdff7cd299f06d69d467a9be55c5d26cc95")
```

</details>

#### BLAKE2s key=00..07 in='Hi There' out=32

- BLAKE2s key=00..07 in='Hi There' out=32
   - Expected: _bytes_to_hex(digest) equals `fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLAKE2s key=00..07 in='Hi There' out=32")
# Reference (Python hashlib.blake2s, key=bytes(range(8))):
#   fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747
val key = _range_bytes(8)
val msg = _hi_there_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BLAKE2b RFC 7693 Appendix A test vectors, BLAKE2s RFC 7693 Appendix B test vectors, BLAKE2 keyed-mode KATs (blake2-kat.json).
- BLAKE2b RFC 7693 Appendix A test vectors
- BLAKE2s RFC 7693 Appendix B test vectors
- BLAKE2 keyed-mode KATs (blake2-kat.json)

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

- Canonical SPipe generation for source `5b69e91ce3179b06386cf270aa5c9373034defb7be02d2f09c1debe8d1b3d267`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b69e91ce3179b06386cf270aa5c9373034defb7be02d2f09c1debe8d1b3d267`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b69e91ce3179b06386cf270aa5c9373034defb7be02d2f09c1debe8d1b3d267`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/blake2_rfc7693_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/blake2_rfc7693_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/blake2_rfc7693_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Appendix A 'abc' unkeyed digest (64 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multi-block: 128 bytes of 'a' unkeyed (1 full block, 64-byte digest)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Appendix B 'abc' unkeyed digest (32 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
