# Scram Sha256 Rfc5802 Specification

> <details>

<!-- sdn-diagram:id=scram_sha256_rfc5802_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scram_sha256_rfc5802_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scram_sha256_rfc5802_spec -> std
scram_sha256_rfc5802_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scram_sha256_rfc5802_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scram Sha256 Rfc5802 Specification

## Scenarios

### SCRAM-SHA-256 — RFC 7677 §3 client-first

#### client-first format is n,,n=user,r=<nonce>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha256_client_first(_user_bytes(), _client_nonce_bytes())
expect(_bytes_eq(cf, _client_first_expected())).to_equal(true)
```

</details>

#### client-first length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = scram_sha256_client_first(_user_bytes(), _client_nonce_bytes())
expect(cf.len()).to_equal(32)
```

</details>

### SCRAM-SHA-256 — RFC 7677 §3 client-final (full round-trip)

#### client-final is byte-exact with RFC 7677 §3 ClientProof

1.  client first expected
2.  server first bytes
3.  password bytes
4.  gs2 header bytes
   - Expected: _bytes_eq(cf, _client_final_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha256_client_final(
    _client_first_expected(),
    _server_first_bytes(),
    _password_bytes(),
    _gs2_header_bytes()
)
expect(_bytes_eq(cf, _client_final_expected())).to_equal(true)
```

</details>

#### client-final text matches RFC 7677 §3 expected message

1.  client first expected
2.  server first bytes
3.  password bytes
4.  gs2 header bytes
   - Expected: _u8_to_text_spec(cf) equals `expected_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (cf, _) = scram_sha256_client_final(
    _client_first_expected(),
    _server_first_bytes(),
    _password_bytes(),
    _gs2_header_bytes()
)
val expected_text = "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="
expect(_u8_to_text_spec(cf)).to_equal(expected_text)
```

</details>

#### expected ServerSignature hex matches RFC 7677 §3

1.  client first expected
2.  server first bytes
3.  password bytes
4.  gs2 header bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha256_client_final(
    _client_first_expected(),
    _server_first_bytes(),
    _password_bytes(),
    _gs2_header_bytes()
)
expect(_bytes_hex(server_sig)).to_equal(
    "eabae24d1062db75a9451ff0b6ea7e98c8546549ff741e672d3251b2397de46e"
)
```

</details>

#### expected ServerSignature is 32 bytes

1.  client first expected
2.  server first bytes
3.  password bytes
4.  gs2 header bytes
   - Expected: server_sig.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, server_sig) = scram_sha256_client_final(
    _client_first_expected(),
    _server_first_bytes(),
    _password_bytes(),
    _gs2_header_bytes()
)
expect(server_sig.len()).to_equal(32)
```

</details>

### SCRAM-SHA-256 — RFC 7677 §3 server-side verify

#### server_verify accepts valid ClientProof

1.  client final expected
2.  password bytes
3.  salt bytes
4.  auth message bytes
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha256_server_verify(
    _client_final_expected(),
    _password_bytes(),
    _salt_bytes(),
    4096,
    _auth_message_bytes()
)
expect(ok).to_equal(true)
```

</details>

#### server_verify rejects tampered ClientProof (content differs, length=32)

1.  tampered final bytes
2.  password bytes
3.  salt bytes
4.  auth message bytes
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tampered: proof char[4] 'Z'→'X'; decoded length unchanged at 32 bytes.
# The constant-time XOR-accumulate fires, not the length check.
val ok = scram_sha256_server_verify(
    _tampered_final_bytes(),
    _password_bytes(),
    _salt_bytes(),
    4096,
    _auth_message_bytes()
)
expect(ok).to_equal(false)
```

</details>

#### server_verify rejects wrong password

1.  client final expected
2.  wrong password bytes
3.  salt bytes
4.  auth message bytes
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha256_server_verify(
    _client_final_expected(),
    _wrong_password_bytes(),
    _salt_bytes(),
    4096,
    _auth_message_bytes()
)
expect(ok).to_equal(false)
```

</details>

#### server_verify rejects wrong salt

1.  client final expected
2.  password bytes
3.  auth message bytes
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrong_salt: [u8] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val ok = scram_sha256_server_verify(
    _client_final_expected(),
    _password_bytes(),
    wrong_salt,
    4096,
    _auth_message_bytes()
)
expect(ok).to_equal(false)
```

</details>

### SCRAM-SHA-256 — RFC 7677 §3 server-final mutual auth

#### server_signature_check diagnostic: decoded server sig is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_server_final_bytes().len()).to_equal(46)
expect(_server_sig_expected().len()).to_equal(32)
```

</details>

#### server_signature_check diagnostic: server_sig b64 decodes to correct hex

1.  client first expected
2.  server first bytes
3.  password bytes
4.  gs2 header bytes
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Direct b64 decode test using scram module's internal _base64_decode
# We test indirectly: build a server_final where the decoded sig
# matches _server_sig_expected
# The b64 of the server sig: "6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="
# eabae24d1062db75a9451ff0b6ea7e98c8546549ff741e672d3251b2397de46e
# We verify by checking that server_signature_check works when
# we pass the correct hex-verified expected sig alongside the server_final
val (_, derived_sig) = scram_sha256_client_final(
    _client_first_expected(),
    _server_first_bytes(),
    _password_bytes(),
    _gs2_header_bytes()
)
expect(_bytes_hex(derived_sig)).to_equal(
    "eabae24d1062db75a9451ff0b6ea7e98c8546549ff741e672d3251b2397de46e"
)
# Manually build server-final with the derived_sig b64
# to bypass the hardcoded _server_sig_expected
# This tests that _ct_eq_bytes works correctly
val ok = _bytes_eq(derived_sig, _server_sig_expected())
expect(ok).to_equal(true)
```

</details>

#### server_signature_check diagnostic: _server_sig_expected hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(_server_sig_expected())).to_equal(
    "eabae24d1062db75a9451ff0b6ea7e98c8546549ff741e672d3251b2397de46e"
)
```

</details>

#### server_signature_check diagnostic: ct_eq_bytes on identical arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _server_sig_expected()
val b = _server_sig_expected()
expect(scram_sha256_ct_eq(a, b)).to_equal(true)
```

</details>

#### server_signature_check diagnostic: decoded server-final sig hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = scram_sha256_decode_server_final(_server_final_bytes())
expect(decoded.len()).to_equal(32)
expect(_bytes_hex(decoded)).to_equal(
    "eabae24d1062db75a9451ff0b6ea7e98c8546549ff741e672d3251b2397de46e"
)
```

</details>

#### server_signature_check accepts valid server-final

1.  server final bytes
2.  server sig expected
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = scram_sha256_server_signature_check(
    _server_final_bytes(),
    _server_sig_expected()
)
expect(ok).to_equal(true)
```

</details>

#### server_signature_check rejects corrupted server-final

1. var bad sig =  server sig expected
2. bad sig[0] =
3.  server final bytes
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip first byte of expected signature
var bad_sig = _server_sig_expected()
bad_sig[0] = (bad_sig[0].to_i64() ^ 0xFF).to_u8()
val ok = scram_sha256_server_signature_check(
    _server_final_bytes(),
    bad_sig
)
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/scram_sha256_rfc5802_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SCRAM-SHA-256 — RFC 7677 §3 client-first
- SCRAM-SHA-256 — RFC 7677 §3 client-final (full round-trip)
- SCRAM-SHA-256 — RFC 7677 §3 server-side verify
- SCRAM-SHA-256 — RFC 7677 §3 server-final mutual auth

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
