# Ssh Transport Specification

> <details>

<!-- sdn-diagram:id=ssh_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_transport_spec -> std
ssh_transport_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Transport Specification

## Scenarios

### SSH transport KEXINIT parsing

#### parses a valid SSH version string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = ssh_parse_version_string(ssh_build_version_string())
expect(version.is_ok()).to_equal(true)
expect(version.unwrap()).to_equal("SSH-2.0-SimpleOS_1.0")
```

</details>

#### returns Err for a version string without CRLF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = ssh_parse_version_string(_hex_decode("5353482d322e302d53696d706c654f535f312e30"))
expect(version.is_err()).to_equal(true)
expect(version.err().unwrap()).to_equal("no CRLF terminator in version string")
```

</details>

#### returns Err for a non-SSH-2.0 version prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = ssh_parse_version_string(_hex_decode("5353482d312e352d4c65676163790d0a"))
expect(version.is_err()).to_equal(true)
expect(version.err().unwrap()).to_equal("unsupported SSH version")
```

</details>

#### parses the canonical transport KEXINIT payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.kex_algorithms).to_equal("curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com")
expect(kex.server_host_key_algorithms).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256")
expect(kex.encryption_client_to_server).to_equal("aes256-gcm@openssh.com")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
expect(kex.mac_client_to_server).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
expect(kex.mac_server_to_client).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
expect(kex.compression_client_to_server).to_equal("none")
expect(kex.compression_server_to_client).to_equal("none")
```

</details>

#### parses repeated canonical KEXINIT payloads consistently

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
expect(parsed.unwrap().server_host_key_algorithms).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256")
```

</details>

#### returns Err for a KEXINIT with the wrong message type

- var payload = ssh build kexinit
   - Expected: parsed.is_err() is true
   - Expected: parsed.err().unwrap() equals `not a KEXINIT message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload = ssh_build_kexinit()
payload[0] = 21
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("not a KEXINIT message")
```

</details>

#### returns Err for a truncated KEXINIT name-list

- truncated push
   - Expected: parsed.is_err() is true
   - Expected: parsed.err().unwrap() equals `KEXINIT: bad lang2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit()
var truncated: [u8] = []
var i: u64 = 0
while i + 8 < payload.len():
    truncated.push(payload[i])
    i = i + 1
val parsed = ssh_parse_kexinit(truncated)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("KEXINIT: bad lang2")
```

</details>

#### returns Err for a KEXINIT with trailing bytes after reserved

- var payload = ssh build kexinit
- payload push
   - Expected: parsed.is_err() is true
   - Expected: parsed.err().unwrap() equals `KEXINIT: trailing bytes after reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload = ssh_build_kexinit()
payload.push(0xAA)
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("KEXINIT: trailing bytes after reserved")
```

</details>

#### returns Err for a KEXINIT with a truncated reserved field

- var payload = ssh build kexinit
- payload pop
   - Expected: parsed.is_err() is true
   - Expected: parsed.err().unwrap() equals `KEXINIT: truncated reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload = ssh_build_kexinit()
payload.pop()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("KEXINIT: truncated reserved")
```

</details>

#### returns Err for a KEXINIT with a non-zero reserved field

- var payload = ssh build kexinit
   - Expected: parsed.is_err() is true
   - Expected: parsed.err().unwrap() equals `KEXINIT: non-zero reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload = ssh_build_kexinit()
val reserved_offset = payload.len() - 4
payload[reserved_offset + 3] = 1
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("KEXINIT: non-zero reserved")
```

</details>

### SSH transport algorithm negotiation

#### honors client preference order for host key algorithms

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = _kex_init(
    "curve25519-sha256",
    "ecdsa-sha2-nistp256,ssh-ed25519,rsa-sha2-256",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519,ecdsa-sha2-nistp256",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.host_key).to_equal("ecdsa-sha2-nistp256")
expect(algos.kex).to_equal("curve25519-sha256")
expect(algos.cipher_c2s).to_equal("aes128-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes128-gcm@openssh.com")
```

</details>

#### falls back to ssh-ed25519 when stronger client preferences are unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = _kex_init(
    "curve25519-sha256",
    "rsa-sha2-512,ecdsa-sha2-nistp256,ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
expect(negotiated.unwrap().host_key).to_equal("ssh-ed25519")
```

</details>

#### accepts OpenSSH MAC lists when AES-GCM is negotiated

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = _kex_init(
    "curve25519-sha256",
    "ssh-ed25519,rsa-sha2-256",
    "chacha20-poly1305@openssh.com,aes128-gcm@openssh.com",
    "chacha20-poly1305@openssh.com,aes128-gcm@openssh.com",
    "umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256",
    "umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256",
    "none,zlib@openssh.com",
    "none,zlib@openssh.com"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.cipher_c2s).to_equal("aes128-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes128-gcm@openssh.com")
expect(algos.mac_c2s).to_equal("none")
expect(algos.mac_s2c).to_equal("none")
```

</details>

#### prefers aes256-gcm when both peers advertise it

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = _kex_init(
    "curve25519-sha256",
    "ssh-ed25519",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.cipher_c2s).to_equal("aes256-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes256-gcm@openssh.com")
expect(algos.mac_c2s).to_equal("none")
expect(algos.mac_s2c).to_equal("none")
```

</details>

#### returns Err when the client and server share no host key algorithm

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = _kex_init(
    "curve25519-sha256",
    "rsa-sha2-256,rsa-sha2-512",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_err()).to_equal(true)
expect(negotiated.err().unwrap()).to_equal("no matching host key algorithm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSH transport KEXINIT parsing
- SSH transport algorithm negotiation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
