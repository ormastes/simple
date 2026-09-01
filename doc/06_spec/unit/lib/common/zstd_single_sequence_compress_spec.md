# Zstd Single Sequence Compress Specification

> Tests covering zstd repeated-tail encoder fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Single Sequence Compress Specification

## Scenarios

### zstd repeated-tail encoder fallback

#### keeps the host-rejected direct-weight single-stream candidate on the raw-block path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the host-rejected direct-weight single-stream candidate on the raw-block path
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: encoded.len() equals `6 + 3 + payload.len()`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the host-rejected direct-weight single-stream candidate on the raw-block path")
val payload = _fresh_table_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(encoded.len()).to_equal(6 + 3 + payload.len())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps level 1 on the raw-block path for the bounded fresh-table lane

- keeps level 1 on the raw-block path for the bounded fresh-table lane
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps level 1 on the raw-block path for the bounded fresh-table lane")
val payload = _fresh_table_payload()
val options = _with_level(default_compression_options(CompressionCodec.zstd), 1)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### keeps repeated tails on the raw-block path until a host-valid sequence encoder exists

- keeps repeated tails on the raw-block path until a host-valid sequence encoder exists
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: encoded.len() equals `6 + 3 + payload.len()`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps repeated tails on the raw-block path until a host-valid sequence encoder exists")
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(encoded.len()).to_equal(6 + 3 + payload.len())
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### fails closed on an exact host-zstd fresh-table single-stream frame with one predefined-table sequence

- fails closed on an exact host-zstd fresh-table single-stream frame with one predefined-table sequence
   - Expected: HOST_VALID_FRESH_TABLE_FRAME[9] & 0x03u8 equals `0x02u8`
   - Expected: (HOST_VALID_FRESH_TABLE_FRAME[9] >> 2u8) & 0x03u8 equals `0x00u8`
   - Expected: HOST_VALID_FRESH_TABLE_FRAME[64] equals `0x01u8`
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on an exact host-zstd fresh-table single-stream frame with one predefined-table sequence")
expect(HOST_VALID_FRESH_TABLE_FRAME[9] & 0x03u8).to_equal(0x02u8)
expect((HOST_VALID_FRESH_TABLE_FRAME[9] >> 2u8) & 0x03u8).to_equal(0x00u8)
expect(HOST_VALID_FRESH_TABLE_FRAME[64]).to_equal(0x01u8)
val decoded = zstd_decompress_frame(HOST_VALID_FRESH_TABLE_FRAME)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

#### emits the exact raw-block frame bytes for repeated tails

- emits the exact raw-block frame bytes for repeated tails
   - Expected: encoded equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the exact raw-block frame bytes for repeated tails")
val payload = _repeated_tail_payload()
val encoded = zstd_compress_frame(payload, default_compression_options(CompressionCodec.zstd))
expect(encoded).to_equal([
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x20u8,
    0x0Cu8,
    0x61u8, 0x00u8, 0x00u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8,
    0x61u8, 0x62u8, 0x63u8
])
```

</details>

#### keeps level 1 on the raw-block fallback

- keeps level 1 on the raw-block fallback
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps level 1 on the raw-block fallback")
val payload = _repeated_tail_payload()
val options = _with_level(default_compression_options(CompressionCodec.zstd), 1)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### preserves checksum on the repeated-tail raw-block fallback

- preserves checksum on the repeated-tail raw-block fallback
   - Expected: (encoded[6] & 0x07u8) equals `0x01u8`
   - Expected: zstd_decompress_frame(encoded).unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves checksum on the repeated-tail raw-block fallback")
val payload = _repeated_tail_payload()
val options = _with_checksum(default_compression_options(CompressionCodec.zstd), true)
val encoded = zstd_compress_frame(payload, options)
expect((encoded[6] & 0x07u8)).to_equal(0x01u8)
expect(zstd_decompress_frame(encoded).unwrap()).to_equal(payload)
```

</details>

#### fails closed on the host-rejected direct-weight single-stream candidate

- fails closed on the host-rejected direct-weight single-stream candidate
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on the host-rejected direct-weight single-stream candidate")
val frame = _host_rejected_direct_weight_frame()
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "trailing bits")
```

</details>

#### host zstd rejects the direct-weight candidate bytes

- host zstd rejects the direct-weight candidate bytes
   - Expected: run.exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("host zstd rejects the direct-weight candidate bytes")
_ensure_tmp_root()
val compressed_path = TMP_ROOT + "/direct_weight_candidate.zst"
_write_hex_file(compressed_path, HOST_REJECTED_DIRECT_WEIGHT_FRAME_HEX)
val run = shell("zstd -q -d -f '" + compressed_path + "' -o '" + compressed_path + ".out'")
expect(run.exit_code != 0).to_equal(true)
```

</details>

#### host zstd accepts the pinned fresh-table single-stream frame

- host zstd accepts the pinned fresh-table single-stream frame
   - Expected: run.exit_code equals `0`
   - Expected: _read_bytes(output_path) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("host zstd accepts the pinned fresh-table single-stream frame")
_ensure_tmp_root()
val compressed_path = TMP_ROOT + "/host_valid_fresh_table_frame.zst"
val output_path = TMP_ROOT + "/host_valid_fresh_table_frame.out"
_write_hex_file(compressed_path, HOST_VALID_FRESH_TABLE_FRAME_HEX)
val run = shell("zstd -q -d -f '" + compressed_path + "' -o '" + output_path + "'")
if run.exit_code != 0:
    print(run.stdout)
    print(run.stderr)
expect(run.exit_code).to_equal(0)
expect(_read_bytes(output_path)).to_equal([
    0x54u8, 0x68u8, 0x69u8, 0x73u8, 0x20u8, 0x69u8, 0x73u8, 0x20u8,
    0x61u8, 0x20u8, 0x73u8, 0x68u8, 0x6Fu8, 0x72u8, 0x74u8, 0x20u8,
    0x65u8, 0x6Eu8, 0x67u8, 0x6Cu8, 0x69u8, 0x73u8, 0x68u8, 0x20u8,
    0x73u8, 0x65u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x63u8, 0x65u8,
    0x20u8, 0x77u8, 0x69u8, 0x74u8, 0x68u8, 0x20u8, 0x72u8, 0x65u8,
    0x70u8, 0x65u8, 0x61u8, 0x74u8, 0x65u8, 0x64u8, 0x20u8, 0x6Cu8,
    0x65u8, 0x74u8, 0x74u8, 0x65u8, 0x72u8, 0x73u8, 0x20u8, 0x61u8,
    0x6Eu8, 0x64u8, 0x20u8, 0x73u8, 0x70u8, 0x61u8, 0x63u8, 0x65u8,
    0x73u8, 0x2Eu8, 0x20u8, 0x54u8, 0x68u8, 0x69u8, 0x73u8, 0x20u8,
    0x69u8, 0x73u8, 0x20u8, 0x61u8, 0x20u8, 0x73u8, 0x68u8, 0x6Fu8,
    0x72u8, 0x74u8, 0x20u8, 0x65u8, 0x6Eu8, 0x67u8, 0x6Cu8, 0x69u8,
    0x73u8, 0x68u8, 0x20u8, 0x73u8, 0x65u8, 0x6Eu8, 0x74u8, 0x65u8,
    0x6Eu8, 0x63u8, 0x65u8, 0x20u8, 0x77u8, 0x69u8, 0x74u8, 0x68u8,
    0x20u8, 0x72u8, 0x65u8, 0x70u8, 0x65u8, 0x61u8, 0x74u8, 0x65u8,
    0x64u8, 0x20u8, 0x6Cu8, 0x65u8, 0x74u8, 0x74u8, 0x65u8, 0x72u8,
    0x73u8, 0x20u8, 0x61u8, 0x6Eu8, 0x64u8, 0x20u8, 0x73u8, 0x70u8,
    0x61u8, 0x63u8, 0x65u8, 0x73u8, 0x2Eu8, 0x20u8
])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/zstd_single_sequence_compress_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd repeated-tail encoder fallback.
- zstd repeated-tail encoder fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `ee99e11cdc382c9b2273ddc554055a40bf67349fe59a962b3736e5893e5bfa7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee99e11cdc382c9b2273ddc554055a40bf67349fe59a962b3736e5893e5bfa7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee99e11cdc382c9b2273ddc554055a40bf67349fe59a962b3736e5893e5bfa7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/zstd_single_sequence_compress_spec.spl
mirror: doc/06_spec/unit/lib/common/zstd_single_sequence_compress_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/zstd_single_sequence_compress_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/zstd_single_sequence_compress_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/zstd_single_sequence_compress_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/zstd_single_sequence_compress_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the host-rejected direct-weight single-stream candidate on the raw-block path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_single_sequence_compress_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps level 1 on the raw-block path for the bounded fresh-table lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_single_sequence_compress_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps repeated tails on the raw-block path until a host-valid sequence encoder exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
