# Zstd Frame Variants Specification

> Tests covering zstd frame header variants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Frame Variants Specification

## Scenarios

### zstd frame header variants

#### keeps the current pure-Simple framed subset in parity across scalar avx2 and neon tiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the current pure-Simple framed subset in parity across scalar avx2 and neon tiers
   - Expected: avx2 equals `scalar`
   - Expected: neon equals `scalar`
   - Expected: zstd_compress_frame(payload, options) equals `scalar`
   - Expected: zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap() equals `payload`
   - Expected: zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap() equals `payload`
   - Expected: zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap() equals `payload`
   - Expected: zstd_decompress_frame(scalar).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the current pure-Simple framed subset in parity across scalar avx2 and neon tiers")
val payload = [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8, 0x66u8]
val options = default_compression_options(CompressionCodec.zstd)
val scalar = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.scalar)
val avx2 = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.avx2)
val neon = zstd_compress_frame_for_tier(payload, options, CompressionSimdTier.neon)
expect(avx2).to_equal(scalar)
expect(neon).to_equal(scalar)
expect(zstd_compress_frame(payload, options)).to_equal(scalar)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap()).to_equal(payload)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap()).to_equal(payload)
expect(zstd_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap()).to_equal(payload)
expect(zstd_decompress_frame(scalar).unwrap()).to_equal(payload)
```

</details>

#### emits frame-level content checksums for the current encoder path

- emits frame-level content checksums for the current encoder path
   - Expected: (encoded[4] & 0x04u8) != 0u8 is true
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits frame-level content checksums for the current encoder path")
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: true,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
val payload = [0x41u8, 0x42u8, 0x43u8, 0x44u8, 0x45u8]
val encoded = zstd_compress_frame(payload, options)
expect((encoded[4] & 0x04u8) != 0u8).to_equal(true)
val decoded = zstd_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### emits the checksum trailer even for empty payloads

- emits the checksum trailer even for empty payloads
   - Expected: (encoded[4] & 0x04u8) != 0u8 is true
   - Expected: encoded.len() equals `13`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the checksum trailer even for empty payloads")
val base = default_compression_options(CompressionCodec.zstd)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: true,
    block_mode: base.block_mode,
    dictionary_bytes: base.dictionary_bytes,
    dictionary_id: base.dictionary_id,
    content_size: base.content_size
)
val encoded = zstd_compress_frame([], options)
expect((encoded[4] & 0x04u8) != 0u8).to_equal(true)
expect(encoded.len()).to_equal(13)
val decoded = zstd_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([])
```

</details>

#### emits the compact 1-byte single-segment size form for small payloads

- emits the compact 1-byte single-segment size form for small payloads
   - Expected: encoded[4] equals `0x20u8`
   - Expected: encoded[5] equals `payload.len().to_u8()`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the compact 1-byte single-segment size form for small payloads")
val payload = [0x61u8, 0x62u8, 0x63u8]
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0x20u8)
expect(encoded[5]).to_equal(payload.len().to_u8())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### emits the compact 2-byte single-segment size form once the payload reaches 256 bytes

- emits the compact 2-byte single-segment size form once the payload reaches 256 bytes
   - Expected: encoded[4] equals `0x60u8`
   - Expected: encoded[5] equals `(payload.len() - 256).to_u8()`
   - Expected: encoded[6] equals `0u8`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the compact 2-byte single-segment size form once the payload reaches 256 bytes")
val payload = _repeated_bytes(0x5Au8, 300)
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0x60u8)
expect(encoded[5]).to_equal((payload.len() - 256).to_u8())
expect(encoded[6]).to_equal(0u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps the 4-byte single-segment size form for larger payloads

- keeps the 4-byte single-segment size form for larger payloads
   - Expected: encoded[4] equals `0xA0u8`
   - Expected: encoded[5] equals `(payload.len() & 0xFF).to_u8()`
   - Expected: encoded[6] equals `((payload.len() >> 8) & 0xFF).to_u8()`
   - Expected: encoded[7] equals `((payload.len() >> 16) & 0xFF).to_u8()`
   - Expected: encoded[8] equals `((payload.len() >> 24) & 0xFF).to_u8()`
   - Expected: (encoded[9] & 0x07u8) equals `0x03u8`
   - Expected: encoded[12] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the 4-byte single-segment size form for larger payloads")
val payload = rt_bytes_alloc(65792)
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded[4]).to_equal(0xA0u8)
expect(encoded[5]).to_equal((payload.len() & 0xFF).to_u8())
expect(encoded[6]).to_equal(((payload.len() >> 8) & 0xFF).to_u8())
expect(encoded[7]).to_equal(((payload.len() >> 16) & 0xFF).to_u8())
expect(encoded[8]).to_equal(((payload.len() >> 24) & 0xFF).to_u8())
expect((encoded[9] & 0x07u8)).to_equal(0x03u8)
expect(encoded[12]).to_equal(0u8)
```

</details>

#### decodes the repeated-tail raw-block fallback

- decodes the repeated-tail raw-block fallback
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes the repeated-tail raw-block fallback")
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 1-byte content size

- decodes single-segment frames with 1-byte content size
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes single-segment frames with 1-byte content size")
val payload = [0x61u8, 0x62u8, 0x63u8]
val frame = _frame(0x20u8, [payload.len().to_u8()], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 8-byte content size

- decodes single-segment frames with 8-byte content size
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes single-segment frames with 8-byte content size")
val payload = [0x21u8, 0x22u8, 0x23u8, 0x24u8, 0x25u8]
val frame = _frame(0xE0u8, _write_u64_le(payload.len().to_u64()), payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes single-segment frames with 2-byte content size

- decodes single-segment frames with 2-byte content size
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes single-segment frames with 2-byte content size")
val payload = _repeated_bytes(0x5Au8, 300)
val encoded_size = payload.len() - 256
val frame = _frame(
    0x60u8,
    [
        (encoded_size & 0xFF).to_u8(),
        ((encoded_size >> 8) & 0xFF).to_u8()
    ],
    payload,
    false
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes non-single-segment frames with a window descriptor

- decodes non-single-segment frames with a window descriptor
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes non-single-segment frames with a window descriptor")
val payload = [0x41u8, 0x42u8, 0x43u8, 0x44u8]
val frame = _frame(0x00u8, [0x00u8], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### verifies frame-level content checksums

- verifies frame-level content checksums
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies frame-level content checksums")
val payload = [0x31u8, 0x32u8, 0x33u8, 0x34u8]
val frame = _frame(0x24u8, [payload.len().to_u8()], payload, true)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### rejects dictionary-backed frames explicitly

- rejects dictionary-backed frames explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dictionary-backed frames explicitly")
val payload = [0x51u8, 0x52u8]
val frame = _frame(0x21u8, [0x09u8, payload.len().to_u8()], payload, false)
_expect_error_contains(decompress_bytes(frame, Some(CompressionCodec.zstd)), "UnsupportedFeature", "dictionary")
```

</details>

#### decodes dictionary-backed frames when the matching external dictionary is supplied directly

- decodes dictionary-backed frames when the matching external dictionary is supplied directly
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes dictionary-backed frames when the matching external dictionary is supplied directly")
val frame = ZSTD_MAGIC_BYTES + [
    0xA3u8,
    0x78u8, 0x56u8, 0x34u8, 0x12u8,
    0x0Cu8, 0x00u8, 0x00u8, 0x00u8,
    0x61u8, 0x00u8, 0x00u8,
    0x48u8, 0x45u8, 0x4Cu8, 0x4Cu8,
    0x4Fu8, 0x5Fu8, 0x44u8, 0x49u8,
    0x43u8, 0x54u8, 0x21u8, 0x21u8
]
val decoded = zstd_decompress_frame_with_dictionary(frame, DICT_OK, DICT_OK_ID)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x48u8, 0x45u8, 0x4Cu8, 0x4Cu8,
    0x4Fu8, 0x5Fu8, 0x44u8, 0x49u8,
    0x43u8, 0x54u8, 0x21u8, 0x21u8
])
```

</details>

#### fails closed when a dictionary-backed frame is decoded with the wrong dictionary id

- fails closed when a dictionary-backed frame is decoded with the wrong dictionary id


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a dictionary-backed frame is decoded with the wrong dictionary id")
val frame = ZSTD_MAGIC_BYTES + [
    0x21u8,
    0x09u8,
    0x03u8,
    0x23u8, 0x00u8, 0x00u8,
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8,
    0x01u8
]
_expect_error_contains(zstd_decompress_frame_with_dictionary(frame, DICT_OK, 8), "CorruptStream", "dictionary id mismatch")
```

</details>

#### accepts frames that carry an explicit zero dictionary id

- accepts frames that carry an explicit zero dictionary id
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts frames that carry an explicit zero dictionary id")
val payload = [0x71u8, 0x72u8]
val frame = _frame(0x21u8, [0x00u8, payload.len().to_u8()], payload, false)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

#### decodes concatenated frames in one buffer

- decodes concatenated frames in one buffer
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes concatenated frames in one buffer")
val left = _frame(0x20u8, [2u8], [0x61u8, 0x62u8], false)
val right = _frame(0x20u8, [3u8], [0x63u8, 0x64u8, 0x65u8], false)
val decoded = decompress_bytes(left + right, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8])
```

</details>

#### fails closed on a corrupt content checksum

- fails closed on a corrupt content checksum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a corrupt content checksum")
val payload = [0x90u8, 0x91u8, 0x92u8]
var frame = _frame(0x24u8, [payload.len().to_u8()], payload, true)
frame[frame.len() - 1] = frame[frame.len() - 1] ^ 0x01u8
_expect_error_contains(decompress_bytes(frame, Some(CompressionCodec.zstd)), "ChecksumMismatch", "checksum")
```

</details>

#### decodes a host-generated frame for a mixed payload

- decodes a host-generated frame for a mixed payload
   - Expected: run.exit_code equals `0`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a host-generated frame for a mixed payload")
_ensure_tmp_root()
var payload: [u8] = []
var i = 0
while i < 4096:
    payload.push(((i * 17 + (i / 7)) % 251).to_u8())
    payload.push(0x61u8 + (i % 5).to_u8())
    payload.push(0x61u8 + (i % 5).to_u8())
    payload.push(0x20u8)
    i = i + 1
val input_path = TMP_ROOT + "/mixed.bin"
val compressed_path = TMP_ROOT + "/mixed.zst"
_write_bytes(input_path, payload)
val run = shell("zstd -q --no-check -19 -f '" + input_path + "' -o '" + compressed_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
val decoded = decompress_bytes(_read_bytes(compressed_path), Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(payload)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/zstd_frame_variants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd frame header variants.
- zstd frame header variants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `70ec88ecd63a2666ab267f80131ef0a15029270e5d428822b6cb7bffe477a29d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70ec88ecd63a2666ab267f80131ef0a15029270e5d428822b6cb7bffe477a29d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70ec88ecd63a2666ab267f80131ef0a15029270e5d428822b6cb7bffe477a29d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/zstd_frame_variants_spec.spl
mirror: doc/06_spec/unit/lib/common/zstd_frame_variants_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/zstd_frame_variants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/zstd_frame_variants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/zstd_frame_variants_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/zstd_frame_variants_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the current pure-Simple framed subset in parity across scalar avx2 and neon tiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_frame_variants_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits frame-level content checksums for the current encoder path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_frame_variants_spec.spl:235:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the checksum trailer even for empty payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
