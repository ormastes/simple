# Scram Sha512 Specification

> <details>

<!-- sdn-diagram:id=scram_sha512_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scram_sha512_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scram_sha512_spec -> string
scram_sha512_spec -> std
scram_sha512_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scram_sha512_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scram Sha512 Specification

## Scenarios

### SCRAM-SHA-512 — client-first

#### client-first format is n,,n=user,r=<nonce>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha512_client_first(_user_bytes_512(), _client_nonce_bytes_512())
expect(_bytes_eq_512(cf, _client_first_expected_512())).to_equal(true)
```

</details>

#### client-first length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha512_client_first(_user_bytes_512(), _client_nonce_bytes_512())
expect(cf.len()).to_equal(32)
```

</details>

### SCRAM-SHA-512 — client-final (full round-trip)

#### client-final is byte-exact with computed ClientProof

1.  client first expected 512
2.  server first bytes 512
3.  password bytes 512
4.  gs2 header bytes 512
   - Expected: _bytes_eq_512(cf, _client_final_expected_512()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha512_client_final(
    _client_first_expected_512(),
    _server_first_bytes_512(),
    _password_bytes_512(),
    _gs2_header_bytes_512()
)
expect(_bytes_eq_512(cf, _client_final_expected_512())).to_equal(true)
```

</details>

#### client-final text matches expected message with SHA-512 proof

1.  client first expected 512
2.  server first bytes 512
3.  password bytes 512
4.  gs2 header bytes 512
   - Expected: _u8_to_text_512(cf) equals `expected_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha512_client_final(
    _client_first_expected_512(),
    _server_first_bytes_512(),
    _password_bytes_512(),
    _gs2_header_bytes_512()
)
val expected_text = "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=gMGXRcevScNtxZ6/8lQYpGtnsNAc3mGcmNomv+xnoOMw+3R2xNJdMNnzMlTN8PPC6wdp6dybEmDYXYTxwnYPJQ=="
expect(_u8_to_text_512(cf)).to_equal(expected_text)
```

</details>

#### ServerSignature hex matches Python-computed reference

1.  client first expected 512
2.  server first bytes 512
3.  password bytes 512
4.  gs2 header bytes 512
   - Expected: _bytes_hex_512(server_sig) equals `_server_sig_hex_512()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha512_client_final(
    _client_first_expected_512(),
    _server_first_bytes_512(),
    _password_bytes_512(),
    _gs2_header_bytes_512()
)
expect(_bytes_hex_512(server_sig)).to_equal(_server_sig_hex_512())
```

</details>

#### ServerSignature is 64 bytes

1.  client first expected 512
2.  server first bytes 512
3.  password bytes 512
4.  gs2 header bytes 512
   - Expected: server_sig.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha512_client_final(
    _client_first_expected_512(),
    _server_first_bytes_512(),
    _password_bytes_512(),
    _gs2_header_bytes_512()
)
expect(server_sig.len()).to_equal(64)
```

</details>

### SCRAM-SHA-512 — server-side verify

#### server_verify accepts valid ClientProof

1.  client final expected 512
2.  password bytes 512
3.  salt bytes 512
4.  auth message bytes 512
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha512_server_verify(
    _client_final_expected_512(),
    _password_bytes_512(),
    _salt_bytes_512(),
    4096,
    _auth_message_bytes_512()
)
expect(ok).to_equal(true)
```

</details>

#### server_verify rejects tampered ClientProof (content differs, length=64)

1.  tampered final bytes 512
2.  password bytes 512
3.  salt bytes 512
4.  auth message bytes 512
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha512_server_verify(
    _tampered_final_bytes_512(),
    _password_bytes_512(),
    _salt_bytes_512(),
    4096,
    _auth_message_bytes_512()
)
expect(ok).to_equal(false)
```

</details>

#### server_verify rejects wrong password

1.  client final expected 512
2.  str to u8 512
3.  salt bytes 512
4.  auth message bytes 512
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha512_server_verify(
    _client_final_expected_512(),
    _str_to_u8_512("wrongpassword"),
    _salt_bytes_512(),
    4096,
    _auth_message_bytes_512()
)
expect(ok).to_equal(false)
```

</details>

### SCRAM-SHA-512 — constant-time equality

#### ct_eq returns true for identical 64-byte arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _salt_bytes_512()
val b = _salt_bytes_512()
expect(scram_sha512_ct_eq(a, b)).to_equal(true)
```

</details>

#### ct_eq returns false for arrays differing in one byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _salt_bytes_512()
val b = _salt_with_first_byte_flipped_512()
expect(scram_sha512_ct_eq(a, b)).to_equal(false)
```

</details>

#### ct_eq returns false for different-length arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _str_to_u8_512("abc")
val b = _str_to_u8_512("abcd")
expect(scram_sha512_ct_eq(a, b)).to_equal(false)
```

</details>

### SCRAM-SHA-512 — server-final mutual auth

#### server_signature_check accepts valid server-final

1.  client first expected 512
2.  server first bytes 512
3.  password bytes 512
4.  gs2 header bytes 512
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha512_client_final(
    _client_first_expected_512(),
    _server_first_bytes_512(),
    _password_bytes_512(),
    _gs2_header_bytes_512()
)
val ok = scram_sha512_server_signature_check(_server_final_bytes_512(), server_sig)
expect(ok).to_equal(true)
```

</details>

#### decode_server_final extracts 64-byte ServerSignature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = scram_sha512_decode_server_final(_server_final_bytes_512())
expect(sig.len()).to_equal(64)
```

</details>

#### decoded ServerSignature hex matches Python-computed reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = scram_sha512_decode_server_final(_server_final_bytes_512())
expect(_bytes_hex_512(sig)).to_equal(_server_sig_hex_512())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/scram_sha512_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SCRAM-SHA-512 — client-first
- SCRAM-SHA-512 — client-final (full round-trip)
- SCRAM-SHA-512 — server-side verify
- SCRAM-SHA-512 — constant-time equality
- SCRAM-SHA-512 — server-final mutual auth

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
