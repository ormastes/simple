# SSH RSA Host-Key Signing Specification

> End-to-end test for the `rsa-sha2-256` path in `ssh_sign_exchange_hash`. Verifies that: 1. The function produces a correctly-framed SSH signature blob (algo string + raw-sig string) and that the raw signature verifies against the known SPKI public key. 2. The function returns `Err` when `rsa_pkcs8` is `nil`. 3. The algo-name header embedded in the blob is exactly `"rsa-sha2-256"`.

<!-- sdn-diagram:id=os_ssh_rsa_hostkey_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_ssh_rsa_hostkey_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_ssh_rsa_hostkey_spec -> std
os_ssh_rsa_hostkey_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_ssh_rsa_hostkey_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSH RSA Host-Key Signing Specification

End-to-end test for the `rsa-sha2-256` path in `ssh_sign_exchange_hash`. Verifies that: 1. The function produces a correctly-framed SSH signature blob (algo string + raw-sig string) and that the raw signature verifies against the known SPKI public key. 2. The function returns `Err` when `rsa_pkcs8` is `nil`. 3. The algo-name header embedded in the blob is exactly `"rsa-sha2-256"`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_ssh_rsa_hostkey_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end test for the `rsa-sha2-256` path in `ssh_sign_exchange_hash`.
Verifies that:
  1. The function produces a correctly-framed SSH signature blob
     (algo string + raw-sig string) and that the raw signature
     verifies against the known SPKI public key.
  2. The function returns `Err` when `rsa_pkcs8` is `nil`.
  3. The algo-name header embedded in the blob is exactly `"rsa-sha2-256"`.

tag: system, crypto, ssh

## Scenarios

### ssh_sign_exchange_hash rsa-sha2-256

#### rsa-sha2-256 signs and the raw signature verifies with rsa_sha256_verify

1. var blob = result unwrap

2. var r algo = ssh get text
   - Expected: r_algo.is_ok() is true

3. var algo res = r algo unwrap

4. var r sig = ssh get string
   - Expected: r_sig.is_ok() is true

5. var sig res = r sig unwrap
   - Expected: verified is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
if not _ensure_rsa_fixture():
    return "skip: openssl RSA fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val spki  = _load_bytes(RSA_SPKI)
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)

# Act
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, exchange_hash)

# Assert — signing succeeded
expect(result.is_ok()).to_equal(true)
var blob = result.unwrap()

# Parse algo-name field (offset 0)
var r_algo = ssh_get_text(blob, 0)
expect(r_algo.is_ok()).to_equal(true)
var algo_res = r_algo.unwrap()

# Parse raw-signature field (immediately after algo-name)
var r_sig = ssh_get_string(blob, algo_res.next_offset)
expect(r_sig.is_ok()).to_equal(true)
var sig_res = r_sig.unwrap()
var raw_sig = sig_res.data

# Verify raw signature against SPKI public key
val verified = rsa_sha256_verify(spki, exchange_hash, raw_sig)
expect(verified).to_equal(true)
```

</details>

#### rsa-sha2-256 signing fails when rsa_pkcs8 is nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)

# Act
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, exchange_hash)

# Assert — must return Err
expect(result.is_ok()).to_equal(false)
```

</details>

#### rsa-sha2-256 signature blob has correct algorithm name header

1. var blob = result unwrap

2. var r algo = ssh get text
   - Expected: r_algo.is_ok() is true

3. var algo res = r algo unwrap
   - Expected: algo_name equals `rsa-sha2-256`


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
if not _ensure_rsa_fixture():
    return "skip: openssl RSA fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val exchange_hash = _make_exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)

# Act
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, exchange_hash)
expect(result.is_ok()).to_equal(true)
var blob = result.unwrap()

# Parse and assert algo-name field
var r_algo = ssh_get_text(blob, 0)
expect(r_algo.is_ok()).to_equal(true)
var algo_res = r_algo.unwrap()
var algo_name = algo_res.value
expect(algo_name).to_equal("rsa-sha2-256")
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
