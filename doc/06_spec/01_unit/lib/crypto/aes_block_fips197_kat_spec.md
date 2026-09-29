# Aes Block Fips197 Kat Specification

> Tests covering AES block cipher FIPS 197 Appendix C known-answer tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Block Fips197 Kat Specification

## Scenarios

### AES block cipher FIPS 197 Appendix C known-answer tests

#### C.1 AES-128 encrypts the FIPS 197 block correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- C.1 AES-128 encrypts the FIPS 197 block correctly
   - Expected: _to_i64(ct, 16) equals `_fips_ct128()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("C.1 AES-128 encrypts the FIPS 197 block correctly")
val schedule = aes128_key_expansion(_to_u8(_fips_key128()))
val ct = aes128_encrypt_block(_to_u8(_fips_plaintext()), schedule)
expect(_to_i64(ct, 16)).to_equal(_fips_ct128())
```

</details>

#### C.3 AES-256 encrypts the FIPS 197 block correctly

- C.3 AES-256 encrypts the FIPS 197 block correctly
   - Expected: _to_i64(ct, 16) equals `_fips_ct256()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("C.3 AES-256 encrypts the FIPS 197 block correctly")
val schedule = aes256_key_expansion(_to_u8(_fips_key256()))
val ct = aes256_encrypt_block(_to_u8(_fips_plaintext()), schedule)
expect(_to_i64(ct, 16)).to_equal(_fips_ct256())
```

</details>

#### AES-128 key expansion produces 176 bytes

- AES-128 key expansion produces 176 bytes
   - Expected: schedule.len() equals `176`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AES-128 key expansion produces 176 bytes")
val schedule = aes128_key_expansion(_to_u8(_fips_key128()))
expect(schedule.len()).to_equal(176)
```

</details>

#### AES-256 key expansion produces 240 bytes

- AES-256 key expansion produces 240 bytes
   - Expected: schedule.len() equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AES-256 key expansion produces 240 bytes")
val schedule = aes256_key_expansion(_to_u8(_fips_key256()))
expect(schedule.len()).to_equal(240)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES block cipher FIPS 197 Appendix C known-answer tests.
- AES block cipher FIPS 197 Appendix C known-answer tests

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2830200523e3d328affa00015f40188872478952f3ff8d7f75cd6a031309e09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2830200523e3d328affa00015f40188872478952f3ff8d7f75cd6a031309e09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2830200523e3d328affa00015f40188872478952f3ff8d7f75cd6a031309e09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/aes_block_fips197_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/aes_block_fips197_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/aes_block_fips197_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'C.1 AES-128 encrypts the FIPS 197 block correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'C.3 AES-256 encrypts the FIPS 197 block correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AES-128 key expansion produces 176 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
