# Cose Rfc9052 Kat Specification

> Tests covering COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cose Rfc9052 Kat Specification

## Scenarios

### COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256)

#### round-trip: create then verify succeeds with correct key

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trip: create then verify succeeds with correct key
   - Expected: _mac0_roundtrip_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: create then verify succeeds with correct key")
expect(_mac0_roundtrip_ok()).to_equal(true)
```

</details>

#### round-trip: recovered payload matches original

- round-trip: recovered payload matches original
   - Expected: _mac0_roundtrip_payload_intact() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: recovered payload matches original")
expect(_mac0_roundtrip_payload_intact()).to_equal(true)
```

</details>

#### rejects verification with wrong key (constant-time path)

- rejects verification with wrong key (constant-time path)
   - Expected: _mac0_wrong_key_rejected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects verification with wrong key (constant-time path)")
expect(_mac0_wrong_key_rejected()).to_equal(true)
```

</details>

#### handles empty payload round-trip

- handles empty payload round-trip
   - Expected: _mac0_empty_payload_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty payload round-trip")
expect(_mac0_empty_payload_ok()).to_equal(true)
```

</details>

#### KAT: wire encoding length meets RFC 8152 C.5 minimum (≥63 bytes)

- KAT: wire encoding length meets RFC 8152 C.5 minimum (≥63 bytes)
   - Expected: _mac0_kat_length_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KAT: wire encoding length meets RFC 8152 C.5 minimum (≥63 bytes)")
expect(_mac0_kat_length_ok()).to_equal(true)
```

</details>

#### tampered MAC tag byte is rejected

- tampered MAC tag byte is rejected
   - Expected: _mac0_tampered_tag_rejected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered MAC tag byte is rejected")
expect(_mac0_tampered_tag_rejected()).to_equal(true)
```

</details>

#### tampered payload byte is rejected (MAC recompute mismatch)

- tampered payload byte is rejected (MAC recompute mismatch)
   - Expected: _mac0_tampered_payload_rejected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered payload byte is rejected (MAC recompute mismatch)")
expect(_mac0_tampered_payload_rejected()).to_equal(true)
```

</details>

#### different keys produce different COSE_Mac0 wire bytes

- different keys produce different COSE_Mac0 wire bytes
   - Expected: _mac0_different_keys_different_bytes() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different keys produce different COSE_Mac0 wire bytes")
expect(_mac0_different_keys_different_bytes()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/cose_rfc9052_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256).
- COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `cf96cd2e6dc7988f16bc18aa19175b264723b9f5461a69a6e0fc1539a959a9d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf96cd2e6dc7988f16bc18aa19175b264723b9f5461a69a6e0fc1539a959a9d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf96cd2e6dc7988f16bc18aa19175b264723b9f5461a69a6e0fc1539a959a9d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/cose_rfc9052_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/cose_rfc9052_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/cose_rfc9052_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/cose_rfc9052_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/cose_rfc9052_kat_spec.spl:253:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip: create then verify succeeds with correct key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/cose_rfc9052_kat_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip: recovered payload matches original' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/cose_rfc9052_kat_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects verification with wrong key (constant-time path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
