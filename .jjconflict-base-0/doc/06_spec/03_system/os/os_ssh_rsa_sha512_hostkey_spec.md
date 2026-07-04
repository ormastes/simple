# SSH RSA-SHA2-512 Host Key Signing Specification

> End-to-end test of `ssh_sign_exchange_hash` for the `"rsa-sha2-512"` algorithm. Verifies that the function correctly: as the first SSH string in the signature blob.

<!-- sdn-diagram:id=os_ssh_rsa_sha512_hostkey_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_ssh_rsa_sha512_hostkey_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_ssh_rsa_sha512_hostkey_spec -> std
os_ssh_rsa_sha512_hostkey_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_ssh_rsa_sha512_hostkey_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSH RSA-SHA2-512 Host Key Signing Specification

End-to-end test of `ssh_sign_exchange_hash` for the `"rsa-sha2-512"` algorithm. Verifies that the function correctly: as the first SSH string in the signature blob.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_ssh_rsa_sha512_hostkey_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end test of `ssh_sign_exchange_hash` for the `"rsa-sha2-512"` algorithm.
Verifies that the function correctly:
- Produces a well-formed SSH signature blob when an RSA PKCS#8 key is present.
- Returns an error when the RSA key is absent.
- Encodes the algorithm name `"rsa-sha2-512"` (not `"rsa-sha2-256"` or `"ssh-rsa"`)
  as the first SSH string in the signature blob.
- Produces a raw signature that round-trips through `rsa_sha512_verify`.

tag: system, ssh, crypto

## Scenarios

### os_ssh_rsa_sha512_hostkey: rsa-sha2-512 host key signing

#### rsa-sha2-512 signs and the raw signature verifies with rsa_sha512_verify

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_rsa_fixture():
    return "skip: openssl RSA fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val spki = _load_bytes(RSA_SPKI)
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, exchange_hash)
expect(result.is_ok()).to_equal(true)
val blob = result.unwrap()
expect(blob.len() > 0).to_equal(true)
# Parse the SSH blob: first string is the algo name
val r_algo = ssh_get_text(blob, 0)
expect(r_algo.is_ok()).to_equal(true)
val algo_result = r_algo.unwrap()
expect(algo_result.value).to_equal("rsa-sha2-512")
# Second string is the raw signature bytes
val r_sig = ssh_get_string(blob, algo_result.next_offset)
expect(r_sig.is_ok()).to_equal(true)
val sig_result = r_sig.unwrap()
val raw_sig = sig_result.data
expect(raw_sig.len() > 0).to_equal(true)
# Round-trip verify: raw_sig must verify against exchange_hash with SPKI
val verified = rsa_sha512_verify(spki, exchange_hash, raw_sig)
expect(verified).to_equal(true)
```

</details>

#### rsa-sha2-512 signing fails when rsa_pkcs8 is nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, exchange_hash)
expect(result.is_err()).to_equal(true)
val msg = result.unwrap_err()
expect(msg).to_contain("no RSA key")
```

</details>

#### rsa-sha2-512 algo-header is correct in signature blob

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_rsa_fixture():
    return "skip: openssl RSA fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, exchange_hash)
expect(result.is_ok()).to_equal(true)
val blob = result.unwrap()
val r_algo = ssh_get_text(blob, 0)
expect(r_algo.is_ok()).to_equal(true)
val algo_result = r_algo.unwrap()
# Must be exactly "rsa-sha2-512" — not "rsa-sha2-256" or "ssh-rsa"
expect(algo_result.value).to_equal("rsa-sha2-512")
expect(algo_result.value == "rsa-sha2-256").to_equal(false)
expect(algo_result.value == "ssh-rsa").to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
