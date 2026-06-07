# Sshd Production Session Kexinit Specification

> 1.  seed

<!-- sdn-diagram:id=sshd_production_session_kexinit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sshd_production_session_kexinit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sshd_production_session_kexinit_spec -> std
sshd_production_session_kexinit_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sshd_production_session_kexinit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Production Session Kexinit Specification

## Scenarios

### SSHD production session KEXINIT

#### uses daemon-selected host material and certificates for accepted sessions

1.  seed

2.  ecdsa p256 pkcs8 der
   - Expected: parsed.is_ok() is true
   - Expected: kex.kex_algorithms equals `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com`
   - Expected: kex.server_host_key_algorithms equals `ssh-ed25519-cert-v01@openssh.com,ssh-ed25519,rsa-sha2-256-cert-v01@openssh.co... (full value in folded executable source)`
   - Expected: kex.encryption_client_to_server equals `aes256-gcm@openssh.com`
   - Expected: kex.encryption_server_to_client equals `aes256-gcm@openssh.com`
   - Expected: kex.mac_client_to_server equals `hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none`
   - Expected: kex.mac_server_to_client equals `hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none`


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = sshd_build_production_session_kexinit_for_test(
    true,
    _seed(),
    [9, 10, 11, 12],
    [13, 14, 15, 16],
    _ecdsa_p256_pkcs8_der(),
    [21, 22, 23, 24],
    [31, 32, 33, 34],
    [41, 42, 43, 44]
)

val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.kex_algorithms).to_equal("curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com")
expect(kex.server_host_key_algorithms).to_equal("ssh-ed25519-cert-v01@openssh.com,ssh-ed25519,rsa-sha2-256-cert-v01@openssh.com,rsa-sha2-512-cert-v01@openssh.com,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256")
expect(kex.encryption_client_to_server).to_equal("aes256-gcm@openssh.com")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
expect(kex.mac_client_to_server).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
expect(kex.mac_server_to_client).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
```

</details>

#### does not advertise raw Ed25519 when the production daemon disables it

1.  seed
   - Expected: parsed.is_ok() is true
   - Expected: kex.server_host_key_algorithms equals `rsa-sha2-256,rsa-sha2-512`
   - Expected: kex.encryption_server_to_client equals `aes256-gcm@openssh.com`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = sshd_build_production_session_kexinit_for_test(
    false,
    _seed(),
    [9, 10, 11, 12],
    [13, 14, 15, 16],
    nil,
    nil,
    nil,
    nil
)

val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.server_host_key_algorithms).to_equal("rsa-sha2-256,rsa-sha2-512")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/apps/sshd/sshd_production_session_kexinit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSHD production session KEXINIT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
