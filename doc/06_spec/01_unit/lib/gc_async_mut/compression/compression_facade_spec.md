# Compression Facade Specification

> Tests covering gc_async_mut compression facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compression Facade Specification

## Scenarios

### gc_async_mut compression facades

#### re-exports RLE helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports RLE helpers
   - Expected: rle_decode(rle_encode("aaaabbbcc")) equals `aaaabbbcc`
   - Expected: rle_decode_bytes(rle_encode_bytes([7, 7, 7, 8])) equals `[7, 7, 7, 8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports RLE helpers")
expect(rle_decode(rle_encode("aaaabbbcc"))).to_equal("aaaabbbcc")
expect(rle_decode_bytes(rle_encode_bytes([7, 7, 7, 8]))).to_equal([7, 7, 7, 8])
```

</details>

#### re-exports LZ77 helpers

- re-exports LZ77 helpers
   - Expected: lz77_decompress(compressed) equals `abcabcabc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports LZ77 helpers")
val compressed = lz77_compress("abcabcabc")
expect(lz77_decompress(compressed)).to_equal("abcabcabc")
```

</details>

#### re-exports gzip package helpers

- re-exports gzip package helpers
   - Expected: gzip_is_compressed(compressed) is true
   - Expected: _bytes_equal(decompressed, payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports gzip package helpers")
val payload: [u8] = [0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]
val compressed = gzip_compress(payload, 1)
val decompressed = gzip_decompress(compressed)

expect(gzip_is_compressed(compressed)).to_equal(true)
expect(_bytes_equal(decompressed, payload)).to_equal(true)
expect(crc32_calculate(payload)).to_be_greater_than(0)
```

</details>

#### re-exports brotli encoder and decoder helpers

- re-exports brotli encoder and decoder helpers
   - Expected: decoded.is_err() is false
   - Expected: _bytes_equal(decoded.unwrap(), payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports brotli encoder and decoder helpers")
val payload: [u8] = [0x41u8, 0x42u8, 0x43u8, 0x44u8]
val encoded = brotli_encode_uncompressed(payload)
val decoded = brotli_decode(encoded)

expect(decoded.is_err()).to_equal(false)
expect(_bytes_equal(decoded.unwrap(), payload)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut compression facades.
- gc_async_mut compression facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `90b97df061677a2be390d29ff89f40f7fbee7b42de102118e8e775a2e624e02d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90b97df061677a2be390d29ff89f40f7fbee7b42de102118e8e775a2e624e02d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90b97df061677a2be390d29ff89f40f7fbee7b42de102118e8e775a2e624e02d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/compression/compression_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/compression/compression_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/compression/compression_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports RLE helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports LZ77 helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/compression/compression_facade_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports gzip package helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
