# Compress Facade Harness Specification

> Tests covering common compression facade harness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Facade Harness Specification

## Scenarios

### common compression facade harness

#### round-trips deterministic framed fixtures across every public codec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips deterministic framed fixtures across every public codec


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips deterministic framed fixtures across every public codec")
val payloads = [
    _fixture_empty(),
    _fixture_short(),
    _fixture_mixed(),
    _fixture_repetitive(256),
    _fixture_incompressible(1024),
    _fixture_overlap_heavy(4096)
]
for payload in payloads:
    _assert_auto_round_trip(CompressionCodec.lz4, payload)
    _assert_auto_round_trip(CompressionCodec.zstd, payload)
    _assert_auto_round_trip(CompressionCodec.lzma2, payload)
```

</details>

#### requires an explicit lz4 block hint for deterministic raw-block fixtures

- requires an explicit lz4 block hint for deterministic raw-block fixtures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires an explicit lz4 block hint for deterministic raw-block fixtures")
_assert_lz4_block_round_trip(_fixture_short())
_assert_lz4_block_round_trip(_fixture_repetitive(128))
_assert_lz4_block_round_trip(_fixture_overlap_heavy(2048))
```

</details>

#### keeps the public facade byte-identical with forced scalar avx2 and neon tiers

- keeps the public facade byte-identical with forced scalar avx2 and neon tiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the public facade byte-identical with forced scalar avx2 and neon tiers")
val payload = _fixture_overlap_heavy(8192) + _fixture_incompressible(1024)
_assert_forced_tier_parity(CompressionCodec.lz4, payload)
_assert_forced_tier_parity(CompressionCodec.zstd, payload)
_assert_forced_tier_parity(CompressionCodec.lzma2, payload)
```

</details>

#### returns typed invalid-header and truncation failures through the public facade

- returns typed invalid-header and truncation failures through the public facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns typed invalid-header and truncation failures through the public facade")
val payload = _fixture_repetitive(512)

val lz4 = compress_bytes(payload, default_compression_options(CompressionCodec.lz4))
val zstd = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
val xz = compress_bytes(payload, default_compression_options(CompressionCodec.lzma2))

var bad_lz4 = lz4
bad_lz4[0] = bad_lz4[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_lz4, nil), "InvalidHeader")

var bad_zstd = zstd
bad_zstd[0] = bad_zstd[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_zstd, nil), "InvalidHeader")

var bad_xz = xz
bad_xz[0] = bad_xz[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_xz, nil), "InvalidHeader")

_expect_error_kind(decompress_bytes(lz4.slice(0, lz4.len() - 1), nil), "TruncatedInput")
_expect_error_kind(decompress_bytes(zstd.slice(0, zstd.len() - 1), nil), "TruncatedInput")
_expect_error_kind(decompress_bytes(xz.slice(0, xz.len() - 1), nil), "TruncatedInput")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/compress_facade_harness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering common compression facade harness.
- common compression facade harness

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

- Canonical SPipe generation for source `e9b0ff84d844d64ca1e34f53ce246bf3dd2a8eb81476abea9323cfb8e14b5c8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9b0ff84d844d64ca1e34f53ce246bf3dd2a8eb81476abea9323cfb8e14b5c8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9b0ff84d844d64ca1e34f53ce246bf3dd2a8eb81476abea9323cfb8e14b5c8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/compress_facade_harness_spec.spl
mirror: doc/06_spec/unit/lib/common/compress_facade_harness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/compress_facade_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/compress_facade_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/compress_facade_harness_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips deterministic framed fixtures across every public codec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress_facade_harness_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires an explicit lz4 block hint for deterministic raw-block fixtures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress_facade_harness_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the public facade byte-identical with forced scalar avx2 and neon tiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
