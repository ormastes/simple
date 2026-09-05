# Sha256 Simd Parity Specification

> Tests covering SHA-256 SIMD/scalar parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 Simd Parity Specification

## Scenarios

### SHA-256 SIMD/scalar parity

#### RFC 6234 §8.5 / FIPS 180-4 §B.1 'abc' — both paths match canonical digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- RFC 6234 §8.5 / FIPS 180-4 §B.1 'abc' — both paths match canonical digest
   - Expected: bytes_to_hex(sha256_bytes(abc_bytes)) equals `expected`
   - Expected: bytes_to_hex(sha256_bytes_scalar(abc_bytes)) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RFC 6234 §8.5 / FIPS 180-4 §B.1 'abc' — both paths match canonical digest")
# Canonical: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
val abc_bytes = [0x61, 0x62, 0x63]
val expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
expect(bytes_to_hex(sha256_bytes(abc_bytes))).to_equal(expected)
expect(bytes_to_hex(sha256_bytes_scalar(abc_bytes))).to_equal(expected)
```

</details>

#### 1-byte payload — SIMD == scalar

- 1-byte payload — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1-byte payload — SIMD == scalar")
val msg = _make_n_bytes(1, 0xAA)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 55-byte payload (one-block boundary, no overflow into 2nd block) — SIMD == scalar

- 55-byte payload (one-block boundary, no overflow into 2nd block) — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("55-byte payload (one-block boundary, no overflow into 2nd block) — SIMD == scalar")
val msg = _make_pattern(55)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 56-byte payload (forces 2nd block due to length encoding) — SIMD == scalar

- 56-byte payload (forces 2nd block due to length encoding) — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("56-byte payload (forces 2nd block due to length encoding) — SIMD == scalar")
val msg = _make_pattern(56)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 64-byte payload (exact one-block multiple) — SIMD == scalar

- 64-byte payload (exact one-block multiple) — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("64-byte payload (exact one-block multiple) — SIMD == scalar")
val msg = _make_pattern(64)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 1024-byte payload (16 blocks) — SIMD == scalar

- 1024-byte payload (16 blocks) — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1024-byte payload (16 blocks) — SIMD == scalar")
# Smaller-than-1KiB-spec workhorse to keep interpreter timing tight.
val msg = _make_pattern(1024)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 2048-byte payload (32 blocks, mixed pattern) — SIMD == scalar

- 2048-byte payload (32 blocks, mixed pattern) — SIMD == scalar
   - Expected: bytes_to_hex(sha256_bytes(msg)) equals `bytes_to_hex(sha256_bytes_scalar(msg))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2048-byte payload (32 blocks, mixed pattern) — SIMD == scalar")
val msg = _make_pattern(2048)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/crypto/sha256_simd_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-256 SIMD/scalar parity.
- SHA-256 SIMD/scalar parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `df3d5d4d7a0323898cbea67f583a9107c80a6174e2bb3c9375941238dcf08f7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df3d5d4d7a0323898cbea67f583a9107c80a6174e2bb3c9375941238dcf08f7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df3d5d4d7a0323898cbea67f583a9107c80a6174e2bb3c9375941238dcf08f7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/crypto/sha256_simd_parity_spec.spl
mirror: doc/06_spec/unit/lib/common/crypto/sha256_simd_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/crypto/sha256_simd_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/crypto/sha256_simd_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/crypto/sha256_simd_parity_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RFC 6234 §8.5 / FIPS 180-4 §B.1 'abc' — both paths match canonical digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha256_simd_parity_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1-byte payload — SIMD == scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha256_simd_parity_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '55-byte payload (one-block boundary, no overflow into 2nd block) — SIMD == scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
