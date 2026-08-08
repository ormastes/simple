# X25519mlkem768 Pinned Hybrid Oracle Specification

> Tests covering X25519MLKEM768 pinned three-oracle composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Pinned Hybrid Oracle Specification

## Scenarios

### X25519MLKEM768 pinned three-oracle composition

#### should compare full wire components and the 64-byte secret (REQ-003 REQ-013)

- Verify pinned fixture identity and compare every hybrid component
   - Expected: _field(hybrid, "profile") equals `_HYBRID_ORACLE_PROFILE`
   - Expected: ek.len() equals `1184`
   - Expected: ciphertext.len() equals `1088`
   - Expected: x25519_base(client_private) equals `client_public`
   - Expected: x25519_base(server_private) equals `server_public`
   - Expected: x25519(server_private, client_public) equals `x_secret`
   - Expected: _append_list_bytes(ek, client_public).len() equals `1216`
   - Expected: _append_list_bytes(ciphertext, server_public).len() equals `1120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify pinned fixture identity and compare every hybrid component")
expect(file_hash_sha256(_MLKEM_ORACLE_PATH)).to_equal(
    _MLKEM_ORACLE_SHA256)
expect(file_hash_sha256(_HYBRID_ORACLE_PATH)).to_equal(
    _HYBRID_ORACLE_SHA256)
val mlkem = file_read_text(_MLKEM_ORACLE_PATH)
val hybrid = file_read_text(_HYBRID_ORACLE_PATH)
expect(_field(hybrid, "profile")).to_equal(_HYBRID_ORACLE_PROFILE)
expect(_field(hybrid, "mlkem_vector_sha256")).to_equal(
    _MLKEM_ORACLE_SHA256)
val ek = _hex_list(_field(mlkem, "encapsulation_key_hex"))
val ciphertext = _hex_list(_field(mlkem, "ciphertext_hex"))
val mlkem_secret = _hex_list(_field(mlkem, "shared_secret_hex"))
val client_private = _hex_bytes(_field(hybrid, "client_private_hex"))
val client_public = _hex_bytes(_field(hybrid, "client_public_hex"))
val server_private = _hex_bytes(_field(hybrid, "server_private_hex"))
val server_public = _hex_bytes(_field(hybrid, "server_public_hex"))
val x_secret = _hex_bytes(_field(hybrid, "x25519_shared_secret_hex"))
val expected_hybrid = _hex_list(_field(hybrid,
    "hybrid_shared_secret_hex"))

expect(ek.len()).to_equal(1184)
expect(ciphertext.len()).to_equal(1088)
expect(x25519_base(client_private)).to_equal(client_public)
expect(x25519_base(server_private)).to_equal(server_public)
expect(x25519(server_private, client_public)).to_equal(x_secret)
expect(_append_list_bytes(ek, client_public).len()).to_equal(1216)
expect(_append_list_bytes(ciphertext, server_public).len()).to_equal(1120)
match x25519_mlkem768_combine(mlkem_secret, x_secret):
    case Ok(actual): expect(actual).to_equal(expected_hybrid)
    case Err(reason): fail(reason)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_pinned_hybrid_oracle_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pinned three-oracle composition.
- X25519MLKEM768 pinned three-oracle composition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
