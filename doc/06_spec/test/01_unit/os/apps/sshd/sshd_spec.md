# Sshd Specification

> <details>

<!-- sdn-diagram:id=sshd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sshd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sshd_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sshd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Specification

## Scenarios

### sshd direct runtime integer decoding

#### untags positive file descriptors returned by the baremetal net runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sshd_decode_net_runtime_i32_for_test(8)).to_equal(1)
expect(sshd_decode_net_runtime_i32_for_test(16)).to_equal(2)
```

</details>

#### preserves zero and negative status codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sshd_decode_net_runtime_i32_for_test(0)).to_equal(0)
expect(sshd_decode_net_runtime_i32_for_test(-72)).to_equal(-72)
```

</details>

#### normalizes decoded boot accepts to the boot TCP session handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sshd_normalize_boot_tcp_client_fd_for_test(0)).to_equal(200)
expect(sshd_normalize_boot_tcp_client_fd_for_test(200)).to_equal(200)
expect(sshd_normalize_boot_tcp_client_fd_for_test(1600)).to_equal(200)
expect(sshd_normalize_boot_tcp_client_fd_for_test(-1)).to_equal(-1)
```

</details>

### sshd host key selection

#### keeps Ed25519 advertised when an RSA host key is configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = sshd_build_host_keys_for_session_for_test(true, [1, 2, 3, 4], [9, 10, 11, 12], [13, 14, 15, 16], nil)
expect(host_keys.ed25519_seed != nil).to_equal(true)
expect(host_keys.rsa_pkcs8 != nil).to_equal(true)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512")
```

</details>

#### can advertise RSA only for live lanes that disable Ed25519

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = sshd_build_host_keys_for_session_for_test(false, [1, 2, 3, 4], [9, 10, 11, 12], [13, 14, 15, 16], nil)
expect(host_keys.ed25519_seed == nil).to_equal(true)
expect(host_keys.rsa_pkcs8 != nil).to_equal(true)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("rsa-sha2-256,rsa-sha2-512")
```

</details>

#### includes ECDSA in live host key selection when configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = sshd_build_host_keys_for_session_for_test(true, [1, 2, 3, 4], nil, nil, _ecdsa_p256_pkcs8_der())
expect(host_keys.ecdsa_p256_pkcs8 != nil).to_equal(true)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("ssh-ed25519,ecdsa-sha2-nistp256")
```

</details>

#### advertises daemon-selected host keys and aes256 in production KEXINIT

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = sshd_build_host_keys_for_session_for_test(true, [1, 2, 3, 4], [9, 10, 11, 12], [13, 14, 15, 16], nil)
val parsed = ssh_parse_kexinit(ssh_build_kexinit_for_host_keys(host_keys))
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.server_host_key_algorithms).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512")
expect(kex.encryption_client_to_server).to_equal("aes256-gcm@openssh.com")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/sshd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sshd direct runtime integer decoding
- sshd host key selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
