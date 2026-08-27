# Blake2b Specification

> Tests covering BLAKE2b RFC 7693 unkeyed test vectors, BLAKE2b keyed-mode test vectors (blake2-kat.json).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2b Specification

## Scenarios

### BLAKE2b RFC 7693 unkeyed test vectors

#### empty input unkeyed 64-byte digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty input unkeyed 64-byte digest
   - Expected: _bytes_to_hex(digest) equals `786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee5... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input unkeyed 64-byte digest")
# RFC 7693: BLAKE2b-512("") =
#   786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419
#   d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce
val digest = blake2b(_empty_bytes(), _empty_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce")
```

</details>

#### Appendix B 'abc' unkeyed 64-byte digest

- Appendix B 'abc' unkeyed 64-byte digest
   - Expected: _bytes_to_hex(digest) equals `ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab7... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Appendix B 'abc' unkeyed 64-byte digest")
# RFC 7693 Appendix B:
#   ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1
#   7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
val digest = blake2b(_empty_bytes(), _abc_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
```

</details>

#### 128-byte input (one full block boundary) 64-byte digest

- 128-byte input (one full block boundary) 64-byte digest
   - Expected: _bytes_to_hex(digest) equals `fc328bf04ed0ec3a0ee77e16ef6d87c34f86b6cae8fb2f7ce9e43a570b0a224e5d22eca4e82e5... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("128-byte input (one full block boundary) 64-byte digest")
# Python: hashlib.blake2b(b'a'*128).hexdigest()
#   fc328bf04ed0ec3a0ee77e16ef6d87c34f86b6cae8fb2f7ce9e43a570b0a224
#   e5d22eca4e82e5261c4b4fd4a94c44de0f0cce82e08dc0f91b6d6d0f55b1d92e3
val msg = _repeat_bytes(0x61u8, 128)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("fc328bf04ed0ec3a0ee77e16ef6d87c34f86b6cae8fb2f7ce9e43a570b0a224e5d22eca4e82e5261c4b4fd4a94c44de0f0cce82e08dc0f91b6d6d0f55b1d92e3")
```

</details>

#### 129-byte input (block boundary + 1) 64-byte digest

- 129-byte input (block boundary + 1) 64-byte digest
   - Expected: _bytes_to_hex(digest) equals `2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac8c3... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("129-byte input (block boundary + 1) 64-byte digest")
# Python: hashlib.blake2b(b'a'*129).hexdigest()
#   2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0
#   e8ccff439ac8c3bf8fb3d9b2a2f4f0ef94cf72e2c45d33ff5fb61aef4e97c4daf
val msg = _repeat_bytes(0x61u8, 129)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac8c3bf8fb3d9b2a2f4f0ef94cf72e2c45d33ff5fb61aef4e97c4daf")
```

</details>

#### variable output length: 32-byte digest of 'abc'

- variable output length: 32-byte digest of 'abc'
   - Expected: _bytes_to_hex(digest) equals `bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("variable output length: 32-byte digest of 'abc'")
# Python: hashlib.blake2b(b'abc', digest_size=32).hexdigest()
#   bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319
val digest = blake2b(_empty_bytes(), _abc_bytes(), 32)
expect(_bytes_to_hex(digest)).to_equal("bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319")
```

</details>

### BLAKE2b keyed-mode test vectors (blake2-kat.json)

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
# Python: hashlib.blake2b(b'', key=bytes(range(64))).hexdigest()
#   10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786
#   b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568
val key = _range_bytes(64)
val digest = blake2b(key, _empty_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/blake2b_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BLAKE2b RFC 7693 unkeyed test vectors, BLAKE2b keyed-mode test vectors (blake2-kat.json).
- BLAKE2b RFC 7693 unkeyed test vectors
- BLAKE2b keyed-mode test vectors (blake2-kat.json)

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

- Canonical SPipe generation for source `622206a746574b5f49d4246486bad500cbc738c79750584259b86e73c1133f86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `622206a746574b5f49d4246486bad500cbc738c79750584259b86e73c1133f86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `622206a746574b5f49d4246486bad500cbc738c79750584259b86e73c1133f86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/blake2b_spec.spl
mirror: doc/06_spec/unit/os/crypto/blake2b_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/blake2b_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/blake2b_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/blake2b_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input unkeyed 64-byte digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/blake2b_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Appendix B 'abc' unkeyed 64-byte digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/blake2b_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '128-byte input (one full block boundary) 64-byte digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
