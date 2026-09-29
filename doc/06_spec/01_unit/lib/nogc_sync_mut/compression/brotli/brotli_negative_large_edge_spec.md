# Brotli Negative Large Edge Specification

> Tests covering brotli_decode — malformed stream guards, brotli_encode_uncompressed — large boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Brotli Negative Large Edge Specification

## Scenarios

### brotli_decode — malformed stream guards

#### rejects the reserved all-zero extended WBITS code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### rejects metadata meta blocks in the last-block position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = brotli_decode(_brotli_last_metadata_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "metadata meta block in last position")
```

</details>

#### rejects compressed blocks that use a complex literal prefix code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = brotli_decode(_brotli_complex_literal_prefix_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "complex prefix code")
```

</details>

#### rejects copies that would fall into the unsupported static dictionary tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = brotli_decode(_brotli_static_dictionary_distance_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "static dictionary distance")
```

</details>

### brotli_encode_uncompressed — large boundaries

#### round-trips a 65536-byte payload in a single maximum uncompressed meta block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _patterned_payload(65536)
val encoded = brotli_encode_uncompressed(payload)
val decoded = brotli_decode(encoded)
expect(decoded.is_err()).to_equal(false)
expect(_bytes_equal(decoded.unwrap(), payload)).to_equal(true)
```

</details>

#### round-trips a 65537-byte payload across the uncompressed meta-block split

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _patterned_payload(65537)
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
| Source | `test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering brotli_decode — malformed stream guards, brotli_encode_uncompressed — large boundaries.
- brotli_decode — malformed stream guards
- brotli_encode_uncompressed — large boundaries

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

- Canonical SPipe generation for source `dbc76d3c0789a54f737fce69216db225fa69fa4e86b8c3815ffe949e0384e90a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbc76d3c0789a54f737fce69216db225fa69fa4e86b8c3815ffe949e0384e90a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbc76d3c0789a54f737fce69216db225fa69fa4e86b8c3815ffe949e0384e90a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:112:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects the reserved all-zero extended WBITS code' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:119:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects metadata meta blocks in the last-block position' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:124:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects compressed blocks that use a complex literal prefix code' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:129:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects copies that would fall into the unsupported static dictionary tier' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
