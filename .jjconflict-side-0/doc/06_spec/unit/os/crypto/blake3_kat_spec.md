# Blake3 Kat Specification

> Tests covering BLAKE3 KAT — V1: input_len=0, BLAKE3 KAT — V2: input_len=1, BLAKE3 KAT — V3: input_len=63, BLAKE3 KAT — V4: input_len=1024.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake3 Kat Specification

## Scenarios

### BLAKE3 KAT — V1: input_len=0

#### V1 hash(empty) = af1349b9...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- V1 hash(empty) = af1349b9...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 hash(empty) = af1349b9...")
expect(_bytes_hex(blake3(_v1_input()))).to_equal(
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
)
```

</details>

#### V1 keyed_hash(empty) = 92b2b756...

- V1 keyed_hash(empty) = 92b2b756...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 keyed_hash(empty) = 92b2b756...")
expect(_bytes_hex(blake3_keyed(_make_key(), _v1_input()))).to_equal(
    "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26"
)
```

</details>

#### V1 derive_key(empty) = 2cc39783...

- V1 derive_key(empty) = 2cc39783...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 derive_key(empty) = 2cc39783...")
expect(_bytes_hex(blake3_kdf(_make_context(), _v1_input()))).to_equal(
    "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d"
)
```

</details>

### BLAKE3 KAT — V2: input_len=1

#### V2 hash([0x00]) = 2d3adedff1...

- V2 hash([0x00]) = 2d3adedff1...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V2 hash([0x00]) = 2d3adedff1...")
expect(_bytes_hex(blake3(_v2_input()))).to_equal(
    "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"
)
```

</details>

### BLAKE3 KAT — V3: input_len=63

#### V3 hash(63 bytes) = e9bc37a5...

- V3 hash(63 bytes) = e9bc37a5...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V3 hash(63 bytes) = e9bc37a5...")
expect(_bytes_hex(blake3(_v3_input()))).to_equal(
    "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b"
)
```

</details>

### BLAKE3 KAT — V4: input_len=1024

#### V4 hash(1024 bytes) = 42214739...

- V4 hash(1024 bytes) = 42214739...


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V4 hash(1024 bytes) = 42214739...")
expect(_bytes_hex(blake3(_v4_input()))).to_equal(
    "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/blake3_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BLAKE3 KAT — V1: input_len=0, BLAKE3 KAT — V2: input_len=1, BLAKE3 KAT — V3: input_len=63, BLAKE3 KAT — V4: input_len=1024.
- BLAKE3 KAT — V1: input_len=0
- BLAKE3 KAT — V2: input_len=1
- BLAKE3 KAT — V3: input_len=63
- BLAKE3 KAT — V4: input_len=1024

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

- Canonical SPipe generation for source `87214d22960e4d41c6d252323405846dbb9c102037d873cb75222acc925ed5ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87214d22960e4d41c6d252323405846dbb9c102037d873cb75222acc925ed5ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87214d22960e4d41c6d252323405846dbb9c102037d873cb75222acc925ed5ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/blake3_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/blake3_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/blake3_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/blake3_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/blake3_kat_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 hash(empty) = af1349b9...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/blake3_kat_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 keyed_hash(empty) = 92b2b756...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/blake3_kat_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 derive_key(empty) = 2cc39783...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
