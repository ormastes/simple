# Sshd Production Packet Transcript Specification

> 1.  client version bytes

<!-- sdn-diagram:id=sshd_production_packet_transcript_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sshd_production_packet_transcript_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sshd_production_packet_transcript_spec -> std
sshd_production_packet_transcript_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sshd_production_packet_transcript_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Production Packet Transcript Specification

## Scenarios

### SSHD production packet transcript

#### walks version, KEX, NEWKEYS, service, password auth, and channel packets

1.  client version bytes

2.  server version bytes
   - Expected: sig_blob.is_ok() is true
   - Expected: sig_parts.0 equals `ssh-ed25519`
   - Expected: ed25519_verify(pubkey, exchange_hash, sig_parts.1) is true
   - Expected: reply[0] equals `SSH_MSG_KEX_ECDH_REPLY`
   - Expected: newkeys.len() equals `1`
   - Expected: newkeys[0] equals `21`
   - Expected: service.is_ok() is true
   - Expected: service.unwrap() equals `ssh-userauth`
   - Expected: service_accept[0] equals `6`
   - Expected: auth.is_ok() is true
   - Expected: auth.unwrap().username equals `root`
   - Expected: auth.unwrap().method equals `password`
   - Expected: users.authenticate_password("root", "simpleos") is true
   - Expected: ssh_build_auth_success()[0] equals `52`
   - Expected: open.is_ok() is true
   - Expected: open.unwrap().0 equals `session`
   - Expected: open.unwrap().1 equals `7`
   - Expected: open_confirm[0] equals `91`
   - Expected: ssh_get_u32(open_confirm, 1) equals `7`
   - Expected: shell_request.is_ok() is true
   - Expected: shell_request.unwrap().1 equals `shell`
   - Expected: shell_request.unwrap().2 is true
   - Expected: ssh_build_channel_success(7)[0] equals `99`
   - Expected: data.is_ok() is true
   - Expected: data.unwrap().0 equals `0`
   - Expected: data.unwrap().1 equals `_echo_ssh_line()`
   - Expected: close.is_ok() is true
   - Expected: close.unwrap() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 107 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _ed25519_seed()
val pubkey = ed25519_keypair_from_seed(seed).1
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
expect(host_keys.ed25519_seed != nil).to_equal(true)

val server_version = ssh_parse_version_string(ssh_build_version_string())
expect(server_version.is_ok()).to_equal(true)
expect(server_version.unwrap()).to_equal("SSH-2.0-SimpleOS_1.0")

val client_kexinit = ssh_build_kexinit_for_host_keys(host_keys)
val server_kexinit = ssh_build_kexinit_for_host_keys(host_keys)
val client_kex = ssh_parse_kexinit(client_kexinit)
val server_kex = ssh_parse_kexinit(server_kexinit)
expect(client_kex.is_ok()).to_equal(true)
expect(server_kex.is_ok()).to_equal(true)
val algos = ssh_negotiate_algorithms(client_kex.unwrap(), server_kex.unwrap())
expect(algos.is_ok()).to_equal(true)
expect(algos.unwrap().kex).to_equal("curve25519-sha256")
expect(algos.unwrap().host_key).to_equal("ssh-ed25519")
expect(algos.unwrap().cipher_s2c).to_equal("aes256-gcm@openssh.com")

val client_private = [
    0x11u8, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11
]
val server_private = [
    0x33u8, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
    0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
    0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
    0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33
]
val client_public = ssh_kex_public_from_private(client_private)
val server_public = ssh_kex_public_from_private(server_private)
val kex_init_payload = _build_kex_ecdh_init(client_public)
val parsed_client_public = ssh_parse_kex_ecdh_init(kex_init_payload)
expect(parsed_client_public.is_ok()).to_equal(true)
expect(parsed_client_public.unwrap()).to_equal(client_public)

val shared = ssh_kex_compute_shared(server_private, client_public)
val host_key_blob = ssh_build_ed25519_host_key_blob(pubkey)
val exchange_hash = ssh_kex_compute_exchange_hash(
    _client_version_bytes(),
    _server_version_bytes(),
    client_kexinit,
    server_kexinit,
    host_key_blob,
    client_public,
    server_public,
    shared
)
val sig_blob = ssh_sign_exchange_hash("ssh-ed25519", host_keys, exchange_hash)
expect(sig_blob.is_ok()).to_equal(true)
val sig_parts = _decode_signature_blob(sig_blob.unwrap())
expect(sig_parts.0).to_equal("ssh-ed25519")
expect(ed25519_verify(pubkey, exchange_hash, sig_parts.1)).to_equal(true)

val reply = ssh_build_kex_ecdh_reply(host_key_blob, server_public, sig_blob.unwrap())
expect(reply[0]).to_equal(SSH_MSG_KEX_ECDH_REPLY)
val newkeys = ssh_build_newkeys()
expect(newkeys.len()).to_equal(1)
expect(newkeys[0]).to_equal(21)

val service = ssh_parse_service_request(_build_service_request())
expect(service.is_ok()).to_equal(true)
expect(service.unwrap()).to_equal("ssh-userauth")
val service_accept = ssh_build_service_accept("ssh-userauth")
expect(service_accept[0]).to_equal(6)

val users = sshd_create_default_users()
val auth = ssh_parse_auth_request(_build_password_auth_request("root", "simpleos"))
expect(auth.is_ok()).to_equal(true)
expect(auth.unwrap().username).to_equal("root")
expect(auth.unwrap().method).to_equal("password")
expect(users.authenticate_password("root", "simpleos")).to_equal(true)
expect(ssh_build_auth_success()[0]).to_equal(52)

val open = ssh_parse_channel_open(_build_channel_open(7))
expect(open.is_ok()).to_equal(true)
expect(open.unwrap().0).to_equal("session")
expect(open.unwrap().1).to_equal(7)
val open_confirm = ssh_build_channel_open_confirmation(7, 0, DEFAULT_WINDOW_SIZE, DEFAULT_MAX_PACKET)
expect(open_confirm[0]).to_equal(91)
expect(ssh_get_u32(open_confirm, 1)).to_equal(7)

val shell_request = ssh_parse_channel_request(_build_channel_request(0, "shell", true))
expect(shell_request.is_ok()).to_equal(true)
expect(shell_request.unwrap().1).to_equal("shell")
expect(shell_request.unwrap().2).to_equal(true)
expect(ssh_build_channel_success(7)[0]).to_equal(99)

val data_msg = ssh_build_channel_data(0, _echo_ssh_line())
val data = ssh_parse_channel_data(data_msg)
expect(data.is_ok()).to_equal(true)
expect(data.unwrap().0).to_equal(0)
expect(data.unwrap().1).to_equal(_echo_ssh_line())

val close_msg = ssh_build_channel_close(0)
val close = ssh_parse_channel_close(close_msg)
expect(close.is_ok()).to_equal(true)
expect(close.unwrap()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSHD production packet transcript

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
