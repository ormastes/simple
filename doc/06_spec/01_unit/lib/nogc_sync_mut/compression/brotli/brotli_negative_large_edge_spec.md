# brotli_negative_large_edge_spec

> Verifies the brotli negative large edge behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# brotli_negative_large_edge_spec

Verifies the brotli negative large edge behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the brotli negative large edge behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### brotli_decode — malformed stream guards

#### rejects the reserved all-zero extended WBITS code

- Verify: rejects the reserved all-zero extended WBITS code
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: rejects the reserved all-zero extended WBITS code")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val decoded = brotli_decode(_brotli_reserved_wbits_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "InvalidHeader", "reserved WBITS code")
```

</details>

#### rejects metadata meta blocks in the last-block position

- Verify: rejects metadata meta blocks in the last-block position
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: rejects metadata meta blocks in the last-block position")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val decoded = brotli_decode(_brotli_last_metadata_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "metadata meta block in last position")
```

</details>

#### rejects compressed blocks that use a complex literal prefix code

- Verify: rejects compressed blocks that use a complex literal prefix code
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: rejects compressed blocks that use a complex literal prefix code")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val decoded = brotli_decode(_brotli_complex_literal_prefix_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "complex prefix code")
```

</details>

#### rejects copies that would fall into the unsupported static dictionary tier

- Verify: rejects copies that would fall into the unsupported static dictionary tier
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: rejects copies that would fall into the unsupported static dictionary tier")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val decoded = brotli_decode(_brotli_static_dictionary_distance_stream())
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "static dictionary distance")
```

</details>

### brotli_encode_uncompressed — large boundaries

#### round-trips a 65536-byte payload in a single maximum uncompressed meta block

- Verify: round-trips a 65536-byte payload in a single maximum uncompressed meta block
   - Expected: decoded.is_err() is false
   - Expected: _bytes_equal(decoded.unwrap(), payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: round-trips a 65536-byte payload in a single maximum uncompressed meta block")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _patterned_payload(65536)
val encoded = brotli_encode_uncompressed(payload)
val decoded = brotli_decode(encoded)
expect(decoded.is_err()).to_equal(false)
expect(_bytes_equal(decoded.unwrap(), payload)).to_equal(true)
```

</details>

#### round-trips a 65537-byte payload across the uncompressed meta-block split

- Verify: round-trips a 65537-byte payload across the uncompressed meta-block split
   - Expected: decoded.is_err() is false
   - Expected: _bytes_equal(decoded.unwrap(), payload) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-BROTLI_BROTLI_NEGATIVE_LARGE-001
step("Verify: round-trips a 65537-byte payload across the uncompressed meta-block split")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val payload = _patterned_payload(65537)
val encoded = brotli_encode_uncompressed(payload)
val decoded = brotli_decode(encoded)
expect(decoded.is_err()).to_equal(false)
expect(_bytes_equal(decoded.unwrap(), payload)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eeb786f8477129f7da27c5146164dae04e0cb01f3bb1dc5ba1c04a7c8c74829a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeb786f8477129f7da27c5146164dae04e0cb01f3bb1dc5ba1c04a7c8c74829a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeb786f8477129f7da27c5146164dae04e0cb01f3bb1dc5ba1c04a7c8c74829a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
