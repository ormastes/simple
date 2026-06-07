# Ssh Kex Rsa Contract Specification

> <details>

<!-- sdn-diagram:id=ssh_kex_rsa_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_kex_rsa_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_kex_rsa_contract_spec -> std
ssh_kex_rsa_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_kex_rsa_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Kex Rsa Contract Specification

## Scenarios

### SSH KEX RSA host-key signing via contract

#### produces a rsa-sha2-512 blob that verifies with a real RSA key

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_rsa_fixture():
    return "skip: openssl RSA fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val spki = _load_bytes(RSA_SPKI)
val exchange_hash = _exchange_hash()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, exchange_hash)
expect(result.is_ok()).to_equal(true)
val parts = _decode_sig_blob(result.unwrap())
expect(parts.0).to_equal("rsa-sha2-512")
expect(parts.1.len()).to_be_greater_than(0)
expect(rsa_sha512_verify(spki, exchange_hash, parts.1)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSH KEX RSA host-key signing via contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
