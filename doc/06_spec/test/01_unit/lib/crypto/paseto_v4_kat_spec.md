# Paseto V4 Kat Specification

> <details>

<!-- sdn-diagram:id=paseto_v4_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paseto_v4_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paseto_v4_kat_spec -> std
paseto_v4_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paseto_v4_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paseto V4 Kat Specification

## Scenarios

### PASETO v4.local encrypt — official test vectors

#### 4-E-1: zero nonce, secret payload → exact token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encrypt_4e1()).to_equal(
    "v4.local.AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAr68PS4AXe7If_ZgesdkUMvSwscFlAl1pk5HC0e8kApeaqMfGo_7OpBnwJOAbY9V7WU6abu74MmcUE8YWAiaArVI8XJ5hOb_4v9RmDkneN0S92dx0OW4pgy7omxgf3S8c3LlQg"
)
```

</details>

#### 4-E-2: zero nonce, hidden payload → exact token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encrypt_4e2()).to_equal(
    "v4.local.AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAr68PS4AXe7If_ZgesdkUMvS2csCgglvpk5HC0e8kApeaqMfGo_7OpBnwJOAbY9V7WU6abu74MmcUE8YWAiaArVI8XIemu9chy3WVKvRBfg6t8wwYHK0ArLxxfZP73W_vfwt5A"
)
```

</details>

#### 4-E-3: real nonce, secret payload → exact token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encrypt_4e3()).to_equal(
    "v4.local.32VIErrEkmY4JVILovbmfPXKW9wT1OdQepjMTC_MOtjA4kiqw7_tcaOM5GNEcnTxl60WkwMsYXw6FSNb_UdJPXjpzm0KW9ojM5f4O2mRvE2IcweP-PRdoHjd5-RHCiExR1IK6t6-tyebyWG6Ov7kKvBdkrrAJ837lKP3iDag2hzUPHuMKA"
)
```

</details>

### PASETO v4.local decrypt — round-trip

#### 4-E-1 decrypts to original payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_u8_to_text(_decrypt_4e1())).to_equal(
    "{\"data\":\"this is a secret message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

#### 4-E-3 decrypts to original payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_u8_to_text(_decrypt_4e3())).to_equal(
    "{\"data\":\"this is a secret message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

### PASETO v4.local tamper rejection

#### tampered ciphertext is rejected by BLAKE2b MAC

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tampered_local_ok()).to_equal(false)
```

</details>

### PASETO v4.local footer mismatch rejection

#### wrong footer is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_footer_mismatch_ok()).to_equal(false)
```

</details>

#### correct footer allows decryption

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_footer_correct_ok()).to_equal(true)
```

</details>

### PASETO v4.public sign — official test vectors

#### 4-S-1: sign with no footer → exact token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sign_4s1()).to_equal(
    "v4.public.eyJkYXRhIjoidGhpcyBpcyBhIHNpZ25lZCBtZXNzYWdlIiwiZXhwIjoiMjAyMi0wMS0wMVQwMDowMDowMCswMDowMCJ9bg_XBBzds8lTZShVlwwKSgeKpLT3yukTw6JUz3W4h_ExsQV-P0V54zemZDcAxFaSeef1QlXEFtkqxT1ciiQEDA"
)
```

</details>

#### 4-S-2: sign with footer → exact token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sign_4s2()).to_equal(
    "v4.public.eyJkYXRhIjoidGhpcyBpcyBhIHNpZ25lZCBtZXNzYWdlIiwiZXhwIjoiMjAyMi0wMS0wMVQwMDowMDowMCswMDowMCJ9v3Jt8mx_TdM2ceTGoqwrh4yDFn0XsHvvV_D0DtwQxVrJEBMl0F2caAdgnpKlt4p7xBnx1HcO-SPo8FPp214HDw.eyJraWQiOiJ6VmhNaVBCUDlmUmYyc25FY1Q3Z0ZUaW9lQTlDT2NOeTlEZmdMMVc2MGhhTiJ9"
)
```

</details>

### PASETO v4.public verify — round-trip

#### 4-S-1 verifies and payload matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_u8_to_text(_verify_4s1_payload())).to_equal(
    "{\"data\":\"this is a signed message\",\"exp\":\"2022-01-01T00:00:00+00:00\"}"
)
```

</details>

### PASETO v4.public tamper rejection

#### tampered token signature is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tampered_public_ok()).to_equal(false)
```

</details>

### PASETO bad header rejection

#### v3.local token rejected by v4.local decrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_wrong_header_local_err()).to_equal(true)
```

</details>

#### v3.public token rejected by v4.public verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_wrong_header_public_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/paseto_v4_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
