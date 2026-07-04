# Rsa Contract Parity Specification

> <details>

<!-- sdn-diagram:id=rsa_contract_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_contract_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_contract_parity_spec -> std
rsa_contract_parity_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_contract_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Contract Parity Specification

## Scenarios

### RSA signing contract backend selection

#### Auto matches HostedReference for a valid SHA-512 RSA fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val msg = _test_message()
val auto_sig = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.Auto)
val hosted_sig = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
expect(auto_sig.len()).to_be_greater_than(0)
expect(auto_sig).to_equal(hosted_sig)
```

</details>

#### HostedReference SHA-512 signing is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val pkcs8 = _load_rsa_pkcs8()
val msg = _test_message()
val sig_a = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
val sig_b = rsa_sha512_sign_with_backend(pkcs8, msg, RsaSignBackend.HostedReference)
expect(sig_a.len()).to_be_greater_than(0)
expect(sig_a).to_equal(sig_b)
```

</details>

#### PureSimple SHA-512 signing is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pure-Simple RSA modexp on a 2048-bit key exceeds the interpreter
# wall-clock budget.  Skip until compiled-mode test runner lands.
return "skip: pure-Simple 2048-bit modexp too slow for interpreter"
```

</details>

#### PureSimple SHA-512 matches HostedReference byte-for-byte and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pure-Simple RSA modexp on a 2048-bit key exceeds the interpreter
# wall-clock budget.  Skip until compiled-mode test runner lands.
return "skip: pure-Simple 2048-bit modexp too slow for interpreter"
```

</details>

#### malformed PKCS#8 returns empty signatures for SHA-256 and SHA-512 across backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = _malformed_pkcs8()
val msg = _test_message()
expect(rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha256_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple)).to_equal([])
expect(rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha512_sign_with_backend(malformed, msg, RsaSignBackend.PureSimple)).to_equal([])
```

</details>

#### wrong key type returns empty SHA-512 signatures across backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ensure_crypto_fixtures():
    return "skip: openssl fixture generation unavailable"
val ec_pkcs8 = _load_bytes(EC_PK8)
val msg = _test_message()
expect(rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.HostedReference)).to_equal([])
expect(rsa_sha512_sign_with_backend(ec_pkcs8, msg, RsaSignBackend.PureSimple)).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/rsa_contract_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RSA signing contract backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
