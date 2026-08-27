# Sshd Production Packet Transcript Specification

> Tests covering SSHD production packet transcript.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Production Packet Transcript Specification

## Scenarios

### SSHD production packet transcript

#### walks version, KEX, NEWKEYS, service, password auth, and channel packets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- walks version, KEX, NEWKEYS, service, password auth, and channel packets
   - Expected: server_version.is_ok() is true
   - Expected: server_version.unwrap() equals `SSH-2.0-SimpleOS_1.0`
   - Expected: client_kex.is_ok() is true
   - Expected: server_kex.is_ok() is true
   - Expected: algos.is_ok() is true
   - Expected: algos.unwrap().kex equals `curve25519-sha256`
   - Expected: algos.unwrap().host_key equals `ssh-ed25519`
   - Expected: algos.unwrap().cipher_s2c equals `aes256-gcm@openssh.com`
   - Expected: parsed_client_public.is_ok() is true
   - Expected: parsed_client_public.unwrap() equals `client_public`
   - Expected: sig_blob.is_ok() is true
   - Expected: sig_parts.0 equals `ssh-ed25519`
   - Expected: ed25519_verify(pubkey, exchange_hash, sig_parts.1) is true
   - Expected: reply[0] equals `SSH_MSG_KEX_ECDH_REPLY`
   - Expected: newkeys.len() equals `1`
   - Expected: newkeys[0] equals `21`
   - Expected: service.is_ok() is true
   - Expected: service.unwrap() equals `ssh-userauth`
   - Expected: service_accept[0] equals `6`
   - Expected: auth.is_err() is true
   - Expected: users.authenticate_password("root", "simpleos") is false
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
<summary>Executable SSpec</summary>

Runnable source: 107 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("walks version, KEX, NEWKEYS, service, password auth, and channel packets")
val seed = _ed25519_seed()
val pubkey = ed25519_keypair_from_seed(seed).1
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
assert_not_equal(host_keys.ed25519_seed, nil)

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

val users = configured_test_users()
val auth = ssh_parse_auth_request(_build_password_auth_request("root", "simpleos"))
expect(auth.is_err()).to_equal(true)
expect(users.authenticate_password("root", "simpleos")).to_equal(false)
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSHD production packet transcript.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8781d499c1a064b5eb53275139778e5187d58eb01d9f939ee673f70d2832c3a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8781d499c1a064b5eb53275139778e5187d58eb01d9f939ee673f70d2832c3a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8781d499c1a064b5eb53275139778e5187d58eb01d9f939ee673f70d2832c3a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl
mirror: doc/06_spec/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks version, KEX, NEWKEYS, service, password auth, and channel packets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
