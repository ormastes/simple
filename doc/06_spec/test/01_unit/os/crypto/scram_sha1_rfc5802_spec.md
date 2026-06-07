# Scram Sha1 Rfc5802 Specification

> <details>

<!-- sdn-diagram:id=scram_sha1_rfc5802_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scram_sha1_rfc5802_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scram_sha1_rfc5802_spec -> string
scram_sha1_rfc5802_spec -> std
scram_sha1_rfc5802_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scram_sha1_rfc5802_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scram Sha1 Rfc5802 Specification

## Scenarios

### SCRAM-SHA-1 — client-first

#### client-first format is n,,n=user,r=<nonce>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha1_client_first(_user_bytes_sha1(), _client_nonce_bytes_sha1())
expect(_bytes_eq_sha1(cf, _client_first_expected_sha1())).to_equal(true)
```

</details>

#### client-first length is 38 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha1_client_first(_user_bytes_sha1(), _client_nonce_bytes_sha1())
expect(cf.len()).to_equal(36)
```

</details>

### SCRAM-SHA-1 — client-final (full round-trip)

#### client-final is byte-exact with computed ClientProof

1.  client first expected sha1
2.  server first bytes sha1
3.  password bytes sha1
4.  gs2 header bytes sha1
   - Expected: _bytes_eq_sha1(cf, _client_final_expected_sha1()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha1_client_final(
    _client_first_expected_sha1(),
    _server_first_bytes_sha1(),
    _password_bytes_sha1(),
    _gs2_header_bytes_sha1()
)
expect(_bytes_eq_sha1(cf, _client_final_expected_sha1())).to_equal(true)
```

</details>

#### client-final text matches expected message with SHA-1 proof

1.  client first expected sha1
2.  server first bytes sha1
3.  password bytes sha1
4.  gs2 header bytes sha1
   - Expected: _u8_to_text_sha1(cf) equals `expected_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha1_client_final(
    _client_first_expected_sha1(),
    _server_first_bytes_sha1(),
    _password_bytes_sha1(),
    _gs2_header_bytes_sha1()
)
val expected_text = "c=biws,r=fyko+d2lbbFgONRv9qkxdawL3rfcNHYJY1ZVvWVs7j,p=v0X8v3Bz2T0CJGbJQyF0X+HI4Ts="
expect(_u8_to_text_sha1(cf)).to_equal(expected_text)
```

</details>

#### ServerSignature hex matches RFC 5802 reference

1.  client first expected sha1
2.  server first bytes sha1
3.  password bytes sha1
4.  gs2 header bytes sha1
   - Expected: _bytes_hex_sha1(server_sig) equals `_server_sig_hex_sha1()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha1_client_final(
    _client_first_expected_sha1(),
    _server_first_bytes_sha1(),
    _password_bytes_sha1(),
    _gs2_header_bytes_sha1()
)
expect(_bytes_hex_sha1(server_sig)).to_equal(_server_sig_hex_sha1())
```

</details>

#### ServerSignature is 20 bytes

1.  client first expected sha1
2.  server first bytes sha1
3.  password bytes sha1
4.  gs2 header bytes sha1
   - Expected: server_sig.len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha1_client_final(
    _client_first_expected_sha1(),
    _server_first_bytes_sha1(),
    _password_bytes_sha1(),
    _gs2_header_bytes_sha1()
)
expect(server_sig.len()).to_equal(20)
```

</details>

### SCRAM-SHA-1 — server-side verify

#### server_verify accepts valid ClientProof

1.  client final expected sha1
2.  password bytes sha1
3.  salt bytes sha1
4.  auth message bytes sha1
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha1_server_verify(
    _client_final_expected_sha1(),
    _password_bytes_sha1(),
    _salt_bytes_sha1(),
    4096,
    _auth_message_bytes_sha1()
)
expect(ok).to_equal(true)
```

</details>

#### server_verify rejects tampered ClientProof (content differs, length=20)

1.  tampered final bytes sha1
2.  password bytes sha1
3.  salt bytes sha1
4.  auth message bytes sha1
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha1_server_verify(
    _tampered_final_bytes_sha1(),
    _password_bytes_sha1(),
    _salt_bytes_sha1(),
    4096,
    _auth_message_bytes_sha1()
)
expect(ok).to_equal(false)
```

</details>

#### server_verify rejects wrong password

1.  client final expected sha1
2.  str to u8 sha1
3.  salt bytes sha1
4.  auth message bytes sha1
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha1_server_verify(
    _client_final_expected_sha1(),
    _str_to_u8_sha1("wrongpassword"),
    _salt_bytes_sha1(),
    4096,
    _auth_message_bytes_sha1()
)
expect(ok).to_equal(false)
```

</details>

### SCRAM-SHA-1 — constant-time equality

#### ct_eq returns true for identical byte arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _salt_bytes_sha1()
val b = _salt_bytes_sha1()
expect(scram_sha1_ct_eq(a, b)).to_equal(true)
```

</details>

#### ct_eq returns false for arrays differing in one byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _salt_bytes_sha1()
val b = _salt_with_first_byte_flipped_sha1()
expect(scram_sha1_ct_eq(a, b)).to_equal(false)
```

</details>

#### ct_eq returns false for different-length arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _str_to_u8_sha1("abc")
val b = _str_to_u8_sha1("abcd")
expect(scram_sha1_ct_eq(a, b)).to_equal(false)
```

</details>

### SCRAM-SHA-1 — server-final mutual auth

#### server_signature_check accepts valid server-final

1.  client first expected sha1
2.  server first bytes sha1
3.  password bytes sha1
4.  gs2 header bytes sha1
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha1_client_final(
    _client_first_expected_sha1(),
    _server_first_bytes_sha1(),
    _password_bytes_sha1(),
    _gs2_header_bytes_sha1()
)
val ok = scram_sha1_server_signature_check(_server_final_bytes_sha1(), server_sig)
expect(ok).to_equal(true)
```

</details>

#### decode_server_final extracts 20-byte ServerSignature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = scram_sha1_decode_server_final(_server_final_bytes_sha1())
expect(sig.len()).to_equal(20)
```

</details>

#### decoded ServerSignature hex matches RFC 5802 reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = scram_sha1_decode_server_final(_server_final_bytes_sha1())
expect(_bytes_hex_sha1(sig)).to_equal(_server_sig_hex_sha1())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/scram_sha1_rfc5802_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SCRAM-SHA-1 — client-first
- SCRAM-SHA-1 — client-final (full round-trip)
- SCRAM-SHA-1 — server-side verify
- SCRAM-SHA-1 — constant-time equality
- SCRAM-SHA-1 — server-final mutual auth

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
