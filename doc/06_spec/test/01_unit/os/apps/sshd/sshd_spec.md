# Sshd Specification

> <details>

<!-- sdn-diagram:id=sshd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sshd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sshd_spec -> os
sshd_spec -> std
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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Specification

## Scenarios

### sshd direct runtime integer decoding

#### builds release-mode route through Simple SSH protocol for hosted Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = SshDaemon.release_route_for_target(PureServerHostTarget.HostedLinux)
expect(route.is_ok()).to_equal(true)
val decision = route.unwrap()
expect(decision.uses_simple_protocol).to_equal(true)
expect(decision.allows_native_protocol_bypass).to_equal(false)
```

</details>

#### builds release-mode SSH plan through Simple protocol stages for hosted Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = SshDaemon.release_plan_for_target(PureServerHostTarget.HostedLinux)
expect(plan.release_ready).to_equal(true)
expect(plan.uses_simple_protocol).to_equal(true)
expect(plan.adapter_name).to_equal("hosted-linux-rt-host-access")
expect(plan.version_exchange_stage).to_equal("simple-ssh-version-exchange")
expect(plan.kex_stage).to_equal("simple-ssh-kex")
expect(plan.auth_stage).to_equal("simple-ssh-auth")
expect(plan.channel_stage).to_equal("simple-ssh-channel")
expect(plan.command_stage).to_equal("simple-host-process-exec")
```

</details>

#### builds release-mode SSH plan through the same stages for SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = SshDaemon.release_plan_for_target(PureServerHostTarget.SimpleOS)
expect(plan.release_ready).to_equal(true)
expect(plan.uses_simple_protocol).to_equal(true)
expect(plan.adapter_name).to_equal("simpleos-kernel-host-access")
expect(plan.version_exchange_stage).to_equal("simple-ssh-version-exchange")
expect(plan.command_stage).to_equal("simple-host-process-exec")
```

</details>

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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
