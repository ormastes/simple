# Paseto V4 Kat Specification

> Tests covering PASETO v4.local encrypt — official test vectors, PASETO v4.local decrypt — round-trip, PASETO v4.local tamper rejection, PASETO v4.local footer mismatch rejection, PASETO v4.public sign — official test vectors, PASETO v4.public verify — round-trip, PASETO v4.public tamper rejection, PASETO bad header rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paseto V4 Kat Specification

## Scenarios

### PASETO v4.local encrypt — official test vectors

#### 4-E-1: zero nonce, secret payload → exact token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 4-E-1: zero nonce, secret payload → exact token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-E-1: zero nonce, secret payload → exact token")
expect(_encrypt_4e1()).to_equal(
    "v4.local.AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAr68PS4AXe7If_ZgesdkUMvSwscFlAl1pk5HC0e8kApeaqMfGo_7OpBnwJOAbY9V7WU6abu74MmcUE8YWAiaArVI8XJ5hOb_4v9RmDkneN0S92dx0OW4pgy7omxgf3S8c3LlQg"
)
```

</details>

#### 4-E-2: zero nonce, hidden payload → exact token

- 4-E-2: zero nonce, hidden payload → exact token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-E-2: zero nonce, hidden payload → exact token")
expect(_encrypt_4e2()).to_equal(
    "v4.local.AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAr68PS4AXe7If_ZgesdkUMvS2csCgglvpk5HC0e8kApeaqMfGo_7OpBnwJOAbY9V7WU6abu74MmcUE8YWAiaArVI8XIemu9chy3WVKvRBfg6t8wwYHK0ArLxxfZP73W_vfwt5A"
)
```

</details>

#### 4-E-3: real nonce, secret payload → exact token

- 4-E-3: real nonce, secret payload → exact token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-E-3: real nonce, secret payload → exact token")
expect(_encrypt_4e3()).to_equal(
    "v4.local.32VIErrEkmY4JVILovbmfPXKW9wT1OdQepjMTC_MOtjA4kiqw7_tcaOM5GNEcnTxl60WkwMsYXw6FSNb_UdJPXjpzm0KW9ojM5f4O2mRvE2IcweP-PRdoHjd5-RHCiExR1IK6t6-tyebyWG6Ov7kKvBdkrrAJ837lKP3iDag2hzUPHuMKA"
)
```

</details>

### PASETO v4.local decrypt — round-trip

#### 4-E-1 decrypts to original payload

- 4-E-1 decrypts to original payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-E-1 decrypts to original payload")
expect(_u8_to_text(_decrypt_4e1())).to_equal(
    "{\"data\":\"this is a secret message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

#### 4-E-3 decrypts to original payload

- 4-E-3 decrypts to original payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-E-3 decrypts to original payload")
expect(_u8_to_text(_decrypt_4e3())).to_equal(
    "{\"data\":\"this is a secret message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

### PASETO v4.local tamper rejection

#### the tampered local token actually differs from the original

- the tampered local token actually differs from the original
   - Expected: _tampered_local_is_really_different() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the tampered local token actually differs from the original")
expect(_tampered_local_is_really_different()).to_equal(true)
```

</details>

#### tampered ciphertext is rejected by BLAKE2b MAC

- tampered ciphertext is rejected by BLAKE2b MAC
   - Expected: _tampered_local_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered ciphertext is rejected by BLAKE2b MAC")
expect(_tampered_local_ok()).to_equal(false)
```

</details>

### PASETO v4.local footer mismatch rejection

#### wrong footer is rejected

- wrong footer is rejected
   - Expected: _footer_mismatch_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong footer is rejected")
expect(_footer_mismatch_ok()).to_equal(false)
```

</details>

#### correct footer allows decryption

- correct footer allows decryption
   - Expected: _footer_correct_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("correct footer allows decryption")
expect(_footer_correct_ok()).to_equal(true)
```

</details>

### PASETO v4.public sign — official test vectors

#### 4-S-1: sign with no footer → exact token

- 4-S-1: sign with no footer → exact token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-S-1: sign with no footer → exact token")
expect(_sign_4s1()).to_equal(
    "v4.public.eyJkYXRhIjoidGhpcyBpcyBhIHNpZ25lZCBtZXNzYWdlIiwiZXhwIjoiMjAyMi0wMS0wMVQwMDowMDowMCswMDowMCJ9bg_XBBzds8lTZShVlwwKSgeKpLT3yukTw6JUz3W4h_ExsQV-P0V54zemZDcAxFaSeef1QlXEFtkqxT1ciiQEDA"
)
```

</details>

#### 4-S-2: sign with footer → exact token

- 4-S-2: sign with footer → exact token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-S-2: sign with footer → exact token")
expect(_sign_4s2()).to_equal(
    "v4.public.eyJkYXRhIjoidGhpcyBpcyBhIHNpZ25lZCBtZXNzYWdlIiwiZXhwIjoiMjAyMi0wMS0wMVQwMDowMDowMCswMDowMCJ9v3Jt8mx_TdM2ceTGoqwrh4yDFn0XsHvvV_D0DtwQxVrJEBMl0F2caAdgnpKlt4p7xBnx1HcO-SPo8FPp214HDw.eyJraWQiOiJ6VmhNaVBCUDlmUmYyc25FY1Q3Z0ZUaW9lQTlDT2NOeTlEZmdMMVc2MGhhTiJ9"
)
```

</details>

### PASETO v4.public verify — round-trip

#### 4-S-1 verifies and payload matches

- 4-S-1 verifies and payload matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-S-1 verifies and payload matches")
expect(_u8_to_text(_verify_4s1_payload())).to_equal(
    "{\"data\":\"this is a signed message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

### PASETO v4.public tamper rejection

#### the tampered public token actually differs from the original

- the tampered public token actually differs from the original
   - Expected: _tampered_public_is_really_different() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the tampered public token actually differs from the original")
expect(_tampered_public_is_really_different()).to_equal(true)
```

</details>

#### tampered token signature is rejected

- tampered token signature is rejected
   - Expected: _tampered_public_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered token signature is rejected")
expect(_tampered_public_ok()).to_equal(false)
```

</details>

### PASETO bad header rejection

#### v3.local token rejected by v4.local decrypt

- v3.local token rejected by v4.local decrypt
   - Expected: _wrong_header_local_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("v3.local token rejected by v4.local decrypt")
expect(_wrong_header_local_err()).to_equal(true)
```

</details>

#### v3.public token rejected by v4.public verify

- v3.public token rejected by v4.public verify
   - Expected: _wrong_header_public_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("v3.public token rejected by v4.public verify")
expect(_wrong_header_public_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/paseto_v4_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PASETO v4.local encrypt — official test vectors, PASETO v4.local decrypt — round-trip, PASETO v4.local tamper rejection, PASETO v4.local footer mismatch rejection, PASETO v4.public sign — official test vectors, PASETO v4.public verify — round-trip, PASETO v4.public tamper rejection, PASETO bad header rejection.
- PASETO v4.local encrypt — official test vectors
- PASETO v4.local decrypt — round-trip
- PASETO v4.local tamper rejection
- PASETO v4.local footer mismatch rejection
- PASETO v4.public sign — official test vectors
- PASETO v4.public verify — round-trip
- PASETO v4.public tamper rejection
- PASETO bad header rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `09aa516fb06ecb3d70cd274099cdcc9ab12663cfe96fe79acbce92910e844274`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09aa516fb06ecb3d70cd274099cdcc9ab12663cfe96fe79acbce92910e844274`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09aa516fb06ecb3d70cd274099cdcc9ab12663cfe96fe79acbce92910e844274`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/paseto_v4_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/paseto_v4_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/paseto_v4_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/paseto_v4_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/paseto_v4_kat_spec.spl:277:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '4-E-1: zero nonce, secret payload → exact token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/paseto_v4_kat_spec.spl:284:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '4-E-2: zero nonce, hidden payload → exact token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/paseto_v4_kat_spec.spl:291:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '4-E-3: real nonce, secret payload → exact token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
