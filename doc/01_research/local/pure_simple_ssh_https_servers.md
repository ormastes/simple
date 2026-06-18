<!-- codex-research -->
# Local Research: Pure Simple SSH and HTTPS Servers

## Request

Implement SSH and HTTPS servers whose protocol logic is Pure Simple, support
hosted Linux and SimpleOS, minimize runtime use to OS access through SFFI/RT
boundaries, provide alpha/beta/release modes, and update SPipe/SFFI/RT guidance.

## Current SSH Surface

- `src/os/apps/sshd/sshd.spl` is the SimpleOS SSH daemon entry. It owns the
  daemon object, host-key selection, per-session startup, and user database
  wiring. It already uses Simple protocol modules but imports runtime OS access:
  `rt_boot_tcp_bind`, `rt_boot_tcp_accept_timeout`, and `rt_net_close`.
- `src/os/apps/sshd/ssh_session.spl` owns session state, version exchange,
  KEX, encrypted packet receive/send, authentication, channel handling, shell
  and exec dispatch.
- `src/os/apps/sshd/ssh_cipher.spl` and `ssh_cipher_live.spl` provide SSH packet
  encryption wrappers around AES-GCM/ChaCha20-Poly1305 style packet framing and
  sequence numbers.
- `src/os/apps/sshd/ssh_packet.spl`, `ssh_kex*.spl`, `ssh_auth.spl`,
  `ssh_channel.spl`, `ssh_mac.spl`, and `ssh_hex.spl` are existing Pure Simple
  protocol helpers.
- `src/os/tools/net/ssh_tool_part*.spl` contains a Simple SSH client/tool path.
  It uses `ClientSocket` and helper send/receive wrappers, so it is useful
  parity evidence but is not the main server deliverable.
- `src/app/io/ssh_sffi.spl` and `src/lib/*/io/ssh_sffi.spl` expose runtime SSH
  APIs such as `rt_ssh_connect`, `rt_ssh_auth_password`, `rt_ssh_exec`, SFTP,
  forwarding, and known-host operations. These are full native/SFFI SSH
  protocol APIs today, not just host-access adapters.

## Current HTTPS/TLS/HTTP Surface

- `src/lib/nogc_async_mut/io/tls.spl`, `tls_handshake.spl`, `tls_io.spl`, and
  `tls_common.spl` contain a Simple TLS 1.2 server implementation. The module
  comments describe `TLS_RSA_WITH_AES_128_GCM_SHA256` and state that ECDHE is
  blocked on an `rt_ecdh_agree`-style primitive.
- `src/lib/nogc_async_mut/io/tls_io.spl` is the host I/O layer for TLS records
  and TCP access.
- `src/lib/nogc_sync_mut/io/tls_sffi.spl`, `src/app/io/tls_sffi.spl`, and
  generated family copies expose `rt_tls_client_*` and `rt_tls_server_*` APIs
  backed by native TLS/rustls-style functionality. These currently bypass Pure
  Simple TLS semantics when used directly.
- `src/lib/*/net/http.spl` contains HTTP request/response/client types and URL
  helpers.
- `src/lib/nogc_async_mut/http_server/http_capability_router.spl` shows the
  existing capability-gated server routing style: public Simple policy chooses
  portable/sendfile/zero-copy actions, while host backends provide OS effects.

## Existing Tests and Evidence

SSH has substantial local test coverage:

- `test/01_unit/os/apps/sshd/sshd_spec.spl`
- `test/01_unit/os/apps/sshd/ssh_packet_spec.spl`
- `test/01_unit/os/apps/sshd/ssh_transport_spec.spl`
- `test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl`
- `test/02_integration/os/apps/sshd/ssh_aes256_gcm_packet_spec.spl`
- `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl`
- `test/02_integration/os/apps/sshd/sshd_production_session_kexinit_spec.spl`
- `test/03_system/os/ssh_live_login_in_qemu_spec.spl`

TLS/HTTP coverage exists but appears split by family and scope:

- `test/01_unit/os/tls12/tls12_record_handshake_round_trip_spec.spl`
- `test/01_unit/lib/common/crypto/tls12_prf_kat_spec.spl`
- `test/01_unit/lib/*/tls/tls_facade_spec.spl`
- HTTP server/client specs exist under `test/01_unit/lib/...` and
  `test/02_integration/lib/...`, with generated docs already present in
  `doc/06_spec/test/...` from other lanes.

## Existing Guidance Relevant to This Lane

- `.codex/skills/sp_dev/SKILL.md` already defines alpha/beta/normal naming for
  dual-backend work and instructs docs/skills to stay current when runtime and
  SFFI contracts change.
- `.claude/skills/spipe.md` warns that native-mode SPipe specs are not always a
  reliable oracle for runtime ABI work and recommends pairing interpreter
  coverage with direct native entrypoints using hard `rt_exit` checks.
- `doc/04_architecture/sound_engine.md` is a useful precedent for a layered
  bridge: public Simple policy depends on capability records and backend traits,
  while native runtime surfaces are limited to device/service boundaries.

## Gaps

- The repo has Pure Simple SSH server protocol modules, but hosted Linux support
  is not clearly separated from SimpleOS TCP/socket adapters.
- Existing SSH SFFI wrappers expose whole SSH operations, which conflicts with
  the requested release-mode rule that production should not silently bypass the
  Simple protocol stack.
- The TLS server path is partially Simple but still depends on runtime crypto
  and TCP helpers. Its supported suite is narrower than modern HTTPS
  expectations.
- HTTPS server composition is not yet a single documented release-mode stack:
  HTTP routing, TLS records/handshake, cert/key loading, socket accept, and
  hosted/SimpleOS adapters need a common boundary.
- No feature-specific research, requirement, architecture, design, or system
  specs existed before this lane state file.

## Recommended Implementation Slices

1. Add a shared network host-access interface for accepted byte streams, with
   hosted Linux and SimpleOS adapters.
2. Route SSHD through that host-access interface while keeping existing SimpleOS
   behavior green.
3. Split SSH SFFI into protocol-bypass APIs and host-access adapter APIs; make
   release-mode entrypoints choose the Simple protocol stack.
4. Compose HTTPS server from Simple HTTP request/response/routing plus Simple
   TLS record/handshake modules, using host-access adapters for TCP and
   filesystem/entropy only.
5. Add mode selection as `alpha`, `beta`, and `release`, with release mapped to
   normal single-path Pure Simple protocol execution.
