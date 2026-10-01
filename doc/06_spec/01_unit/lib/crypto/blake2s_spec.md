# Blake2s Specification

> Tests covering BLAKE2s RFC 7693 unkeyed test vectors, BLAKE2s keyed-mode test vectors (blake2-kat.json), BLAKE2s streaming update API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2s Specification

## Scenarios

### BLAKE2s RFC 7693 unkeyed test vectors

#### empty input unkeyed 32-byte digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty input unkeyed 32-byte digest
   - Expected: _bytes_to_hex(digest) equals `69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input unkeyed 32-byte digest")
# RFC 7693: BLAKE2s("") =
#   69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9
val digest = blake2s_hash(_empty_bytes(), 32u32, _empty_bytes())
expect(_bytes_to_hex(digest)).to_equal("69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9")
```

</details>

#### Appendix B 'abc' unkeyed 32-byte digest (RFC 7693 §B)

- Appendix B 'abc' unkeyed 32-byte digest (RFC 7693 §B)
   - Expected: _bytes_to_hex(digest) equals `508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Appendix B 'abc' unkeyed 32-byte digest (RFC 7693 §B)")
# RFC 7693 Appendix B:
#   508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
val digest = blake2s_hash(_empty_bytes(), 32u32, _abc_bytes())
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### 64-byte input (one full block boundary) 32-byte digest

- 64-byte input (one full block boundary) 32-byte digest
   - Expected: _bytes_to_hex(digest) equals `651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("64-byte input (one full block boundary) 32-byte digest")
# Python: hashlib.blake2s(b'a'*64).hexdigest()
#   651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
val msg = _repeat_bytes(0x61u8, 64)
val digest = blake2s_hash(_empty_bytes(), 32u32, msg)
expect(_bytes_to_hex(digest)).to_equal("651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252")
```

</details>

#### 65-byte input (one full block + 1 residual byte) 32-byte digest

- 65-byte input (one full block + 1 residual byte) 32-byte digest
   - Expected: _bytes_to_hex(digest) equals `045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65-byte input (one full block + 1 residual byte) 32-byte digest")
# openssl dgst -blake2s256 on 65 'a' bytes:
#   045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497
# The value previously recorded here (b4ee6ca1ad2ff2...) was NOT the
# BLAKE2s digest of this input — see
# doc/08_tracking/bug/fabricated_blake2s_65_byte_kat_2026-08-04.md.
val msg = _repeat_bytes(0x61u8, 65)
val digest = blake2s_hash(_empty_bytes(), 32u32, msg)
expect(_bytes_to_hex(digest)).to_equal("045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497")
```

</details>

#### variable output length: 16-byte digest of 'abc'

- variable output length: 16-byte digest of 'abc'
   - Expected: _bytes_to_hex(digest) equals `aa4938119b1dc7b87cbad0ffd200d0ae`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("variable output length: 16-byte digest of 'abc'")
# Python: hashlib.blake2s(b'abc', digest_size=16).hexdigest()
#   aa4938119b1dc7b87cbad0ffd200d0ae
val digest = blake2s_hash(_empty_bytes(), 16u32, _abc_bytes())
expect(_bytes_to_hex(digest)).to_equal("aa4938119b1dc7b87cbad0ffd200d0ae")
```

</details>

### BLAKE2s keyed-mode test vectors (blake2-kat.json)

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
# Python: hashlib.blake2s(b'', key=bytes(range(32))).hexdigest()
#   48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49
val key = _range_bytes(32)
val digest = blake2s_hash(key, 32u32, _empty_bytes())
expect(_bytes_to_hex(digest)).to_equal("48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49")
```

</details>

#### BLAKE2s key=00..07 in='Hi There' out=32

- BLAKE2s key=00..07 in='Hi There' out=32
   - Expected: _bytes_to_hex(digest) equals `fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BLAKE2s key=00..07 in='Hi There' out=32")
# Python: hashlib.blake2s(b'Hi There', key=bytes(range(8))).hexdigest()
#   fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747
val key = _range_bytes(8)
val digest = blake2s_hash(key, 32u32, _hi_there_bytes())
expect(_bytes_to_hex(digest)).to_equal("fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747")
```

</details>

### BLAKE2s streaming update API

#### streaming 3-chunk update matches single-call hash for 'abc'

- streaming 3-chunk update matches single-call hash for 'abc'
   - Expected: _bytes_to_hex(digest) equals `508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming 3-chunk update matches single-call hash for 'abc'")
# Feed "a", "b", "c" separately; must equal blake2s_hash([], 32, "abc")
var st = blake2s_init(_empty_bytes(), 32u32)
var chunk_a: [u8] = []
chunk_a.push(0x61u8)
st = blake2s_update(st, chunk_a)
var chunk_b: [u8] = []
chunk_b.push(0x62u8)
st = blake2s_update(st, chunk_b)
var chunk_c: [u8] = []
chunk_c.push(0x63u8)
st = blake2s_update(st, chunk_c)
val digest = blake2s_final(st)
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### streaming 65-byte message in 1+64 chunks matches single-call hash

- streaming 65-byte message in 1+64 chunks matches single-call hash
   - Expected: _bytes_to_hex(streaming_digest) equals `_bytes_to_hex(onecall_digest)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming 65-byte message in 1+64 chunks matches single-call hash")
# Chunk 1: 1 byte 'a', Chunk 2: 64 bytes 'a'
# Exercises the buffer-flush boundary during update.
var st = blake2s_init(_empty_bytes(), 32u32)
var first_chunk: [u8] = []
first_chunk.push(0x61u8)
st = blake2s_update(st, first_chunk)
val rest = _repeat_bytes(0x61u8, 64)
st = blake2s_update(st, rest)
val streaming_digest = blake2s_final(st)
val onecall_digest = blake2s_hash(_empty_bytes(), 32u32, _repeat_bytes(0x61u8, 65))
expect(_bytes_to_hex(streaming_digest)).to_equal(_bytes_to_hex(onecall_digest))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/blake2s_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BLAKE2s RFC 7693 unkeyed test vectors, BLAKE2s keyed-mode test vectors (blake2-kat.json), BLAKE2s streaming update API.
- BLAKE2s RFC 7693 unkeyed test vectors
- BLAKE2s keyed-mode test vectors (blake2-kat.json)
- BLAKE2s streaming update API

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f030d4a7e32f88b633a7ce0bf26fd804b22b05e7b5e4e22fa340202eec3547d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f030d4a7e32f88b633a7ce0bf26fd804b22b05e7b5e4e22fa340202eec3547d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f030d4a7e32f88b633a7ce0bf26fd804b22b05e7b5e4e22fa340202eec3547d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/blake2s_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/blake2s_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/blake2s_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/blake2s_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/blake2s_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input unkeyed 32-byte digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/blake2s_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Appendix B 'abc' unkeyed 32-byte digest (RFC 7693 §B)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/blake2s_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '64-byte input (one full block boundary) 32-byte digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
