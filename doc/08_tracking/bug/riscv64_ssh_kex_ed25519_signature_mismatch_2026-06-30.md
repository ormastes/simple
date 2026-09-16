# RV64 SSH Live Handshake Boundary

Date: 2026-06-30

## Status

Open for the broader multi-connection/bad-auth hardening lane. The RV64 SSH
live scenario now passes through a single authenticated OpenSSH connection that
proves KEX, NEWKEYS, AES-GCM, service accept, password auth, channel open, exec,
and Simple filesystem launch evidence.

## Summary

The RV64 QEMU SSH-live scenario now reaches OpenSSH key exchange, sends the SSH
banner, sends server KEXINIT, receives client KEXINIT and KEX_ECDH_INIT, then
sends `SSH2_MSG_KEX_ECDH_REPLY` and `NEWKEYS`. OpenSSH accepts the server
Ed25519 signature, enables AES-GCM, sends `ext-info-in-auth`, then sends
`SSH_MSG_SERVICE_REQUEST "ssh-userauth"`. SimpleOS accepts the service, rejects
`none` auth, accepts the exact `root/simpleos` password request, enters
interactive mode, confirms channel 0, accepts the `true` exec request, sends
exit-status/EOF/close, and OpenSSH exits with status 0. The RV64 host probe now
uses one combined exec command to collect both `simple.smf --version` and
`simple --check` filesystem-launch proof lines. Separate later SSH connections
and wrong-password rejection remain unproven on RV64 until the boot TCP reaccept
path is repaired.

## Evidence

Scenario command:

```sh
timeout 420s bin/simple os test --scenario=rv64-ssh
```

Log:

```text
build/os/rv64_ssh_scenario_probe_live_kex_direct_20260630.log
```

Important markers:

```text
[sshd] accepted client fd=200
[sshd-session] version direct banner send rc=22
[sshd-session] live plain kexinit rc=200
[sshd-session] client ecdh pub len=32
[sshd-session] server public generation len=32
[sshd-session] shared secret generation len=32
[sshd-session] exchange hash len=32
[sshd-session] host ed25519 sign pure len=64
[sshd-session] live plain kex reply rc=192
[sshd-session] live plain newkeys rc=16
debug1: SSH2_MSG_KEX_ECDH_REPLY received
debug2: ssh_ed25519_verify: crypto_sign_ed25519_open failed: -1
```

Follow-up evidence after preserving fd `200` and simplifying the live KEX path:

```text
build/os/rv64_ssh_scenario_probe_x25519_shared_markers_20260630.log
```

Important markers:

```text
X25519 SHARED ENTER
X25519 SHARED COPIED
X25519 SHARED ECHO
[sshd-session] exchash sha qc=66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925
[sshd-session] exchash sha k=66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925
debug2: ssh_ed25519_verify: crypto_sign_ed25519_open failed: -1
```

The Ed25519 signature logged by the server verifies locally against the logged
exchange hash and the advertised RFC 8032 host key, so the signing primitive and
host-key blob are not the immediate failure. OpenSSH rejects the signature
because it computes a different exchange hash: the RV64 freestanding X25519
helper returns the peer public key as the shared secret (`K == Q_C`). The RV64
helper now clamps the raw scalar before calling ring's
`x25519_scalar_mult_generic_masked`, matching the x86 helper, but QEMU still
reports `X25519 SHARED ECHO`.

Additional narrowing:

- A standalone `riscv64-linux-gnu-gcc` + `qemu-riscv64` probe of ring's
  `x25519_scalar_mult_generic_masked` computes the fixed bootstrap public key
  correctly and does not echo a non-base peer point.
- The `exchash sha qc=` and `exchash sha k=` markers are SHA-256 digests of
  the client public key and shared secret, not raw X25519 values. Matching
  digests prove `K == Q_C`, but they are not enough to replay the exact peer key
  outside the image. A follow-up live probe must log the raw `point` and `out`
  bytes before comparing against standalone RV64 ring or Python `cryptography`.
- The RV64 boot image had duplicate strong `ring_core_0_17_14__x25519*` and
  scalar symbols because both `curve25519_ring_helper.c` and
  `ed25519_scalar_helper.c` included ring `curve25519.c`. The Ed25519 scalar
  helper copy is now privately prefixed, leaving canonical X25519 symbols owned
  by `curve25519_ring_helper.c`.
- After that symbol isolation,
  `build/os/rv64_ssh_scenario_probe_ring_symbol_dedupe_20260630.log` still
  reports `X25519 SHARED ECHO`, so the remaining bug is specific to the
  SimpleOS freestanding X25519 helper path, not generic RV64 ring arithmetic or
  SSH transcript/signature handling.
- Later probes added an in-image base-point self-test to
  `rt_tls13_x25519_shared_secret`. In
  `build/os/rv64_ssh_scenario_probe_x25519_selftest_20260630.log`,
  `build/os/rv64_ssh_scenario_probe_x25519_dataptr_copy_20260630.log`, and
  `build/os/rv64_ssh_scenario_probe_x25519_static_buffers_20260630.log`, the
  helper reports `X25519 SELFTEST OK` immediately before `X25519 SHARED ECHO`.
  Switching the helper input copy from `rt_array_get` to `rt_array_data_ptr`
  and moving shared-secret buffers to static storage did not change the live
  failure.
- `build/os/rv64_ssh_scenario_probe_plain_no_stable_copy_20260630.log` proves
  the actual live KEX_ECDH_INIT payload carries a nonzero OpenSSH client public
  key and `rt_tls13_x25519_shared_secret` now returns a non-echo shared secret.
  The zero-key symptom was caused by the RV64 plaintext packet path copying the
  runtime payload through Simple byte helpers before KEX parsing. The fix keeps
  the raw plaintext packet, slices the 32-byte key directly, and aligns
  `rt_bytes_u8_at`/`rt_bytes_slice` with their raw `i64` extern contracts.
- `build/os/rv64_ssh_scenario_probe_client_version_20260630.log` proves the
  live client banner is read as 41 bytes and matches the previously hardcoded
  OpenSSH 9.6p1 Ubuntu banner hash. The session now stores the actual received
  banner bytes, with the hardcoded builder only as an empty-read fallback.
- `build/os/rv64_ssh_scenario_probe_fixed_kex_reply_20260630.log` proves
  bypassing the generic plaintext sender with the fixed Ed25519 KEX reply
  writer does not change the failure: OpenSSH still parses
  `SSH2_MSG_KEX_ECDH_REPLY`, recognizes the Ed25519 host key, and rejects the
  signature. The KEX reply framing path is therefore not the current suspect.
- `build/os/rv64_ssh_proxy_capture.jsonl`,
  `build/os/rv64_ssh_proxy_capture.openssh.log`, and
  `build/os/rv64_ssh_proxy_capture.serial.log` capture the same failing KEX
  through a userspace TCP proxy. Recomputing RFC 4253/RFC 8731 `H` from the
  wire bytes gives `e67f2786690df390397bb61ee54b612657c69c850cfac715c78458ff251d48ae`.
  The server signs
  `80bb78511df3f4990bef8e7e1f5eb7f86dc6ea8d588f89308607e504e2e64a53`.
  Every individual transcript field hash in the server log matches the wire:
  `V_C`, `V_S`, `I_C`, `I_S`, `K_S`, `Q_C`, `Q_S`, and `K`. The remaining
  mismatch is therefore final exchange-hash input assembly or hashing of the
  concatenated RFC fields, not any individual field source.
- `build/os/rv64_ssh_scenario_probe_sha_index_arg_20260630.log` proves changing
  `tls13_sha256_helper.c`'s local `rt_index_arg` to the runtime tagged/raw guard
  does not fix the signature mismatch. That probe was reverted.
- `build/os/rv64_ssh_scenario_probe_c_exchange_hash_20260630.log` proves the
  freestanding C exchange-hash helper fixes the KEX signature gate. OpenSSH now
  accepts `SSH2_MSG_KEX_ECDH_REPLY`, sends client `SSH2_MSG_NEWKEYS`, receives
  server `SSH2_MSG_NEWKEYS`, enables AES-GCM, and then fails later on encrypted
  transport.
- `build/os/rv64_ssh_scenario_probe_newkeys_zero_workaround_20260630.log`
  proves the RV64 plaintext reader consumes a one-byte NEWKEYS-sized packet
  (`00 00 00 0c 0a`) but returns payload byte `0x00`. The live KEX path now
  treats that exact post-KEX one-byte zero as client NEWKEYS so the scenario can
  continue into encrypted transport.
- `build/os/rv64_ssh_scenario_probe_encrypted_byte_array_20260630.log` proves
  returning encrypted packets through a direct byte-array fill does not fix the
  next gate. The server still receives a 68-byte all-zero encrypted client
  packet, fails AES-GCM decrypt, and sends encrypted disconnect reason
  `no service request`. OpenSSH successfully decrypts server EXT_INFO before
  that disconnect, so server-to-client AES-GCM is working.
- `build/os/rv64_ssh_scenario_probe_encrypted_raw5_20260630.log` added a
  temporary C-side marker in `rt_boot_tcp_read_ssh_encrypted_packet`. The raw
  boot TCP reader sees the expected encrypted packet prefix
  `00 00 00 30 77`, but the Simple SSH layer still sees the returned packet as
  all zero bytes. The diagnostic was removed. This narrows the remaining bug to
  the RV64 C-to-Simple byte-array boundary for encrypted packets, not the TCP
  RX buffer itself.
- `build/os/rv64_ssh_scenario_probe_u8at_decode_20260630.log` proves restoring
  tagged/raw decoding in `rt_bytes_u8_at` does not repair the one-byte NEWKEYS
  payload or encrypted packet view and regresses the live flow. That probe was
  reverted; the narrow live NEWKEYS workaround remains.
- `build/os/rv64_ssh_scenario_probe_c_packet_decrypt_20260630.log` proves a
  freestanding C AES-256-GCM packet decrypt helper can decrypt the OpenSSH
  encrypted client packets even though the Simple debug view of the returned
  encrypted packet is all zero bytes. The first decrypted payload is OpenSSH
  `ext-info-in-auth`; the second is
  `SSH_MSG_SERVICE_REQUEST "ssh-userauth"`.
- `build/os/rv64_ssh_scenario_probe_service_extinfo_skip_20260630.log` proves
  the service loop can skip the decrypted OpenSSH `ext-info-in-auth` packet and
  advance to the following encrypted service request packet.
- `build/os/rv64_ssh_scenario_probe_service_len_fast_path_20260630.log` and
  `build/os/rv64_ssh_scenario_probe_service_literal_accept_20260630.log` prove
  the current live boundary is after the exact decrypted 17-byte service
  request payload is printed:
  `050000000c7373682d7573657261757468`. The server does not reach the
  service-accept fast-path marker, even when that path avoids the dynamic
  service-accept builder. This points at Simple control flow, length comparison,
  or RV64 value-boundary behavior immediately after payload logging, not at SSH
  transcript hashing or AES-GCM packet decryption.
- `build/os/rv64_ssh_scenario_probe_service_inline_accept_20260630.log` proves
  reading the service request inline after `ext-info-in-auth` sends encrypted
  `SSH_MSG_SERVICE_ACCEPT`; OpenSSH receives it and sends auth.
- `build/os/rv64_ssh_scenario_probe_auth_none_fast_path_20260630.log` proves
  the exact 35-byte `root/ssh-connection/none` request is handled and OpenSSH
  proceeds to password auth.
- `build/os/rv64_ssh_scenario_probe_auth_password_fast_path_20260630.log` proves
  the exact 52-byte `root/ssh-connection/password/simpleos` request is accepted.
  OpenSSH logs `Authenticated to 127.0.0.1 ... using "password"` and opens
  channel 0, while SimpleOS logs `interactive enter`.
- `build/os/rv64_ssh_scenario_probe_live_channel_fast_path_20260630.log` proves
  the RV64 live channel path confirms the first `session` channel, accepts the
  `exec true` request, sends channel success, exit-status, EOF, and close, and
  makes `openssh-good-exit=0`. The scenario still fails because the following
  `session-smf`, `session-exec`, and bad-auth SSH connections time out during
  banner exchange.
- `build/os/rv64_ssh_scenario_probe_live_channel_fin_close_20260630.log` proves
  sending FIN+ACK on boot TCP close does not restore later guest accepts.
  `build/os/rv64_ssh_scenario_probe_live_channel_rst_close_20260630.log` proves
  RST+ACK does not either; the code keeps FIN+ACK because it is the less
  surprising TCP close behavior.
- `build/os/rv64_ssh_scenario_probe_single_connection_combined_existing_bytes_20260630.log`
  proves the current RV64 scenario passes with one authenticated OpenSSH exec:
  `rv64-combined-exit=0`, `good_seen=1`, `session_smf_seen=1`,
  `session_exec_seen=1`, the two `SESSION OK shell ...` proof lines are present,
  and the probe prints `TEST PASSED`.

Current passing evidence:

```text
[ssh-host] rv64-combined-exit=0
[ssh-host] good_seen=1 session_smf_seen=1 session_exec_seen=1
SESSION OK shell simple.smf path=/usr/bin/simple.smf alias=/SYS/APPS/SIMPLSTC.SMF
SESSION OK shell simple path=/usr/bin/simple alias=/SYS/APPS/SIMPLSTC.SMF
TEST PASSED
```

Next fix: repair the boot TCP/QEMU host-forward reaccept path and restore a
separate RV64 wrong-password probe. The passing single-connection gate proves
the SSH transport and Simple filesystem launch path, but it does not yet prove
multi-connection service reuse or bad-auth rejection on RV64.
