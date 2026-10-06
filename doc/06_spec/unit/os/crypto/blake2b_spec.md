# BLAKE2b known-answer unit manual: scope and evidence

## Purpose and audience

Crypto/library maintainers use these six scenarios to check one-shot BLAKE2b
against independent digest answers: empty and short input, full-block and
block-plus-one boundaries, shorter output, and keyed empty input.

## Assumptions and primary workflow

The corrected boundary cases use an empty key, a 64-byte output and exactly
128 or 129 ASCII `a` bytes (0x61). Compare each complete hexadecimal digest
with the independent OpenSSL BLAKE2B-512 answer retained in the dated bug.
No streaming API exists on this owner, and no streaming behavior is implied.

## Traceability and recovery

Source: `test/unit/os/crypto/blake2b_spec.spl`; owner: `src/os/crypto/blake2b.spl`.
Existing `REQ-SSPEC-UNIT` metadata is retained without inventing a feature
requirement. If a digest differs, retain exact input bytes, size, key, output
length and provider identity before diagnosing compression/final-block logic.
Do not replace an oracle solely with the implementation's returned digest.

## Evidence and limitations

Current source SHA256: `72e00373f5f1ee2d6ff53b6f7dbe322298203b38b41d1050179b73901f88a701`.
The original legacy row 23664 executed six examples with four passing and
two failing. Independent installed OpenSSL ran once per retained boundary
input; its digests match both actual SPL failure outputs byte-for-byte.
This changed legacy copy independently passed 6/6, zero failures/skips,
under pinned Phase1 seed `0f9bfc1` and frozen dependency source `e59027c`,
with kernel exit 0/quiescent 1. Exact receipts and oracle identities are in
`doc/08_tracking/bug/blake2b_boundary_fixture_oracles_2026-10-07.md`.
This diagnostic seed evidence does not qualify native crypto, security,
constant-time behavior or the whole bootstrap. The generated executable
body is retained below; no passing test is replayed for documentation.

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
   - Expected: _bytes_to_hex(digest) equals `fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047e... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("128-byte input (one full block boundary) 64-byte digest")
# Independent OpenSSL BLAKE2B-512 oracle for exactly 128 ASCII 'a' bytes:
#   fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76
#   b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b
val msg = _repeat_bytes(0x61u8, 128)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b")
```

</details>

#### 129-byte input (block boundary + 1) 64-byte digest

- 129-byte input (block boundary + 1) 64-byte digest
   - Expected: _bytes_to_hex(digest) equals `55e6e0eb418149a8af92fd9ddc99254781b2f522a131b4f4d984404b71a00e1167b8124d5dcdd... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("129-byte input (block boundary + 1) 64-byte digest")
# Independent OpenSSL BLAKE2B-512 oracle for exactly 129 ASCII 'a' bytes:
#   55e6e0eb418149a8af92fd9ddc99254781b2f522a131b4f4d984404b71a00e11
#   67b8124d5dcddd4c6977b299392335d6edd303da6d344d74bbef2d38101b232b
val msg = _repeat_bytes(0x61u8, 129)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("55e6e0eb418149a8af92fd9ddc99254781b2f522a131b4f4d984404b71a00e1167b8124d5dcddd4c6977b299392335d6edd303da6d344d74bbef2d38101b232b")
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
| Updated | 2026-10-06 |
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
