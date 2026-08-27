# Common Compression Framework Facade Specification

> Tests covering common compression facade integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Common Compression Framework Facade Specification

## Scenarios

### common compression facade integration

#### keeps the kernel zstd adapter byte-identical with the public facade on deterministic frames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the kernel zstd adapter byte-identical with the public facade on deterministic frames
   - Expected: facade.is_err() is false
   - Expected: adapter.is_err() is false
   - Expected: adapter.unwrap() equals `facade.unwrap()`
   - Expected: adapter.unwrap() equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the kernel zstd adapter byte-identical with the public facade on deterministic frames")
val payload = _payload(4096)
val encoded = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(false)
expect(adapter.is_err()).to_equal(false)
expect(adapter.unwrap()).to_equal(facade.unwrap())
expect(adapter.unwrap()).to_equal(payload)
```

</details>

#### keeps the kernel zstd adapter aligned with concatenated-frame facade decode

- keeps the kernel zstd adapter aligned with concatenated-frame facade decode
   - Expected: facade.is_err() is false
   - Expected: adapter.is_err() is false
   - Expected: adapter.unwrap() equals `facade.unwrap()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the kernel zstd adapter aligned with concatenated-frame facade decode")
val left = compress_bytes(_payload(256), default_compression_options(CompressionCodec.zstd))
val right = compress_bytes(_payload(384), default_compression_options(CompressionCodec.zstd))
val combined = left + right
val facade = decompress_bytes(combined, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(combined)
expect(facade.is_err()).to_equal(false)
expect(adapter.is_err()).to_equal(false)
expect(adapter.unwrap()).to_equal(facade.unwrap())
```

</details>

#### translates public checksum failures through the kernel adapter deterministically

- translates public checksum failures through the kernel adapter deterministically
   - Expected: facade.is_err() is true
   - Expected: adapter.is_err() is true
   - Expected: adapter.unwrap_err() equals `_error_text(facade.unwrap_err())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("translates public checksum failures through the kernel adapter deterministically")
val payload = _payload(1024)
var encoded = compress_bytes(payload, _zstd_checksum_options())
encoded[encoded.len() - 1] = encoded[encoded.len() - 1] ^ 0x01u8
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(true)
expect(adapter.is_err()).to_equal(true)
expect(adapter.unwrap_err()).to_equal(_error_text(facade.unwrap_err()))
```

</details>

#### translates public invalid-header failures through the kernel adapter deterministically

- translates public invalid-header failures through the kernel adapter deterministically
   - Expected: facade.is_err() is true
   - Expected: adapter.is_err() is true
   - Expected: adapter.unwrap_err() equals `_error_text(facade.unwrap_err())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("translates public invalid-header failures through the kernel adapter deterministically")
val payload = _payload(128)
var encoded = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
encoded[0] = encoded[0] ^ 0x01u8
val facade = decompress_bytes(encoded, Some(CompressionCodec.zstd))
val adapter = zstd_decompress(encoded)
expect(facade.is_err()).to_equal(true)
expect(adapter.is_err()).to_equal(true)
expect(adapter.unwrap_err()).to_equal(_error_text(facade.unwrap_err()))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/core/common_compression_framework_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering common compression facade integration.
- common compression facade integration

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `936b3448d6a519b2db733ef8b38a0811530703f8c59bd6ab48acea1180cda400`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `936b3448d6a519b2db733ef8b38a0811530703f8c59bd6ab48acea1180cda400`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `936b3448d6a519b2db733ef8b38a0811530703f8c59bd6ab48acea1180cda400`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/core/common_compression_framework_facade_spec.spl
mirror: doc/06_spec/integration/core/common_compression_framework_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/core/common_compression_framework_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/core/common_compression_framework_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/core/common_compression_framework_facade_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the kernel zstd adapter byte-identical with the public facade on deterministic frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/core/common_compression_framework_facade_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the kernel zstd adapter aligned with concatenated-frame facade decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/core/common_compression_framework_facade_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates public checksum failures through the kernel adapter deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
