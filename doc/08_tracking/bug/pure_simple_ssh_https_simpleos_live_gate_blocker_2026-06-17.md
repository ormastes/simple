# Pure Simple SSH/HTTPS SimpleOS Live Gate Blocker

Date: 2026-06-17
Lane: pure Simple SSH/HTTPS servers
Status: open

## Scope

This blocker tracks the remaining live SimpleOS evidence gap for the pure
Simple SSH/HTTPS server lane.

Hosted Linux and synthetic SimpleOS host-access adapter evidence is covered by
`test/03_system/lib/pure_simple_ssh_https_servers/pure_simple_server_release_smoke_spec.spl`.
That smoke proves release preflight, release plans, native-bypass rejection,
SSH password auth, SSH channel `exec` request parsing, HTTPS response/routing,
TLS record rejection, and TLS application-data AEAD record evidence.

It does not prove a live SimpleOS QEMU server session.

## Current Live Gate

The current live gate is tracked by:

- `doc/03_plan/os/simpleos/live_gate_vm_decrypt_fail_recovery_2026-06-17.md`
- `doc/08_tracking/bug/live_gate_vm_decrypt_fail_blocker_2026-06-17.md`

The focused live gate command already run in the recovery lane was:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 63 seconds.

Fresh artifacts recorded by the recovery lane:

- `build/os/ssh_live_login_fresh_2026-06-17.log`
- `build/os/x64-ssh-live.serial.log`
- `build/os/x64-ssh-live.openssh-good.txt`
- `build/os/x64-ssh-live.openssh-bad-auth.txt`

## Blocking Condition

The live SSH QEMU gate currently reaches an accepted connection but fails in the
server-side SSH version-exchange path with a zero-byte version read. The gate
does not yet reach encrypted packet receive, so AES-GCM decrypt-fail debugging
is premature for live SimpleOS.

Follow-up serial evidence narrowed the failure to fd ownership:

```text
[sshd] accepted client fd=0
[rt-net] version bytes recv fn sock_fd=0
[rt-net] version bytes recv branch=nil
[sshd-session] version recv bytes len=0
```

`SshDaemon.accept_loop()` was using the raw boot TCP accept path while
`SshSession` reads through the `rt_net_socket_facade` socket table. The accepted
raw fd was therefore not registered for the session read path.

Bounded implementation update: `src/os/apps/sshd/sshd.spl` now routes listener
creation, bind/listen, accept, and close through `rt_net_socket_facade`, keeping
accepted client fds registered before SSH version reads.

Focused non-live verification passed:

```bash
bin/simple check src/os/apps/sshd/sshd.spl src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl
```

A subsequent single live gate after that fix progressed to a registered facade
client fd but still failed before KEX:

```text
[sshd] accepted client fd=1001
[rt-net] version bytes recv fn sock_fd=1001
[rt-net] version bytes recv branch=entry os_fd=0
[sshd-session] version recv bytes len=1153202240580805315
```

That showed a narrower accepted-fd byte-array marshalling failure in
`rt_boot_tcp_take_version_bytes`. The facade has now been updated so
`rt_net_recv_version_bytes()` uses the raw byte helper only for legacy fd `200`;
registered facade fds read through the stable text version path and reconstruct
CRLF-terminated bytes in Simple.

Focused non-live verification after that update passed:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

The next focused live gate still failed before KEX, but showed the registered
facade fd reaching the version text reader while OpenSSH timed out waiting for
the server banner:

```text
[sshd] accepted client fd=1001
[sshd-session] raw_send len=22
[rt-net] send fn sock_fd=1001 len=22
[rt-net] version recv branch=entry os_fd=0
```

Runtime inspection showed the boot TCP helpers expose listener handle `100` and
active-client handle `200`. The facade now maps accepted synthetic client fds to
runtime handle `200` after accept succeeds, so send/read/close calls use the
boot TCP handle supported by the runtime.

Focused non-live verification after that mapping fix passed:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/sshd.spl src/os/apps/sshd/ssh_session.spl
```

The next focused live gate proved the active-client handle mapping reached the
version path (`os_fd=200`) but still timed out during banner exchange:

```text
[sshd] accepted client fd=1001
[sshd-session] raw_send len=22
[rt-net] send fn sock_fd=1001 len=22
[rt-net] version bytes recv branch=entry os_fd=200
```

`SshSession` now sends the SSH identification banner through
`rt_net_send_ssh_banner(sock_fd)`, a facade method that resolves synthetic fds
to the runtime active-client handle before calling the boot TCP banner helper.
This avoids the byte-array send path for the version banner while keeping the
runtime call behind the host-access facade.

Focused non-live verification after that banner-send update passed:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

The next focused live gate proved the facade banner helper returned through the
registered active-client handle, but OpenSSH still timed out during banner
exchange:

```text
[rt-net] banner send entry rc=0
[sshd-session] version banner send rc=0
[rt-net] version bytes recv branch=entry os_fd=200
```

Boot TCP accept readiness has now been tightened in
`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`: accept no longer
returns from a SYN-only poll-count fallback and instead waits until the TCP
processor sees a post-SYN ACK or payload. This prevents SSHD from sending the
server identification banner before the client-side TCP handshake has completed.

Focused non-live verification after that runtime change passed:

```bash
cc -fsyntax-only src/os/kernel/arch/riscv64/boot/freestanding_runtime.c
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

A subsequent focused live gate after the accept-handshake fix still failed
before KEX/decrypt, but progressed further: the Simple session received the
OpenSSH client identification bytes, routed the server banner send through the
facade fd to runtime active-client handle `200`, and then blocked waiting for
the next client bytes while OpenSSH timed out during banner exchange:

```text
[sshd-session] version bytes len=22
[rt-net] banner send fn sock_fd=1001
[rt-net] banner send entry rc=0
[sshd-session] version banner send rc=0
[rt-net] version bytes recv branch=entry os_fd=200
```

The banner helper's prior `rc=0` evidence was ambiguous because the lower TCP
packet helper returned `void`. `rt_send_tcp_packet()` now propagates the
`rt_send_frame()` result, and `rt_boot_tcp_send_ssh_banner()` returns an error
if the banner frame does not submit while logging either:

```text
BTCP SSH BANNER SENT
BTCP SSH BANNER DROP
```

Focused non-live verification after this runtime evidence fix passed:

```bash
cc -fsyntax-only src/os/kernel/arch/riscv64/boot/freestanding_runtime.c
```

The next x64 live gate still failed in about 62.6 seconds and did not show the
new `BTCP SSH BANNER SENT` / `BTCP SSH BANNER DROP` markers. That proved the
previous send-status instrumentation was on the RISC-V boot TCP helper, while
the current failing live gate builds
`examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl` into
`build/os/simpleos_ssh_live_32.elf`.

Symbol inspection of that live ELF showed the x64 image had strong Simple
facade code but only weak stubs for the `rt_boot_tcp_*` bridge names:

```text
T kernel__net__rt_net_socket_facade__rt_net_send_ssh_banner
W rt_boot_tcp_send_ssh_banner
W rt_boot_tcp_take_version_bytes
W rt_boot_tcp_take_version_text
W rt_boot_tcp_write_bytes
```

Bounded implementation update: the x86_64 boot runtime now provides strong
`rt_boot_tcp_*` bridge functions over its existing direct `_sockets[]` TCP
stack, and `rt_net_socket_facade.rt_net_accept()` now stores the actual
accepted runtime fd instead of hardcoding active handle `200`.

Focused non-live verification after the x64 bridge update passed:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl
cc -fsyntax-only examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c
```

The next focused x64 live gate confirmed that the bridge fixed SSH banner
exchange. OpenSSH now receives the server identification and sends KEXINIT:

```text
debug1: Remote protocol version 2.0, remote software version SimpleOS_1.0
debug1: SSH2_MSG_KEXINIT sent
Connection closed by 127.0.0.1 port 2222
```

Serial evidence:

```text
[btcp-x64] accepted fd=1
BTCP SSH BANNER SENT
[sshd-session] version banner send rc=22
[rt-net] version bytes recv branch=entry os_fd=1
[tcp-rx] first-bytes=0x0 0x0 0x4 0x54 0x9 0x14 ...
```

The remaining live failure has moved from banner exchange to KEX packet
handling. The server was reading the 1108-byte client KEXINIT through repeated
1-byte `rt_net_recv_bytes()` calls from Simple. To remove that timeout-prone
path, the x86_64 boot bridge now provides
`rt_boot_tcp_read_ssh_plain_packet_payload()`, and
`rt_net_recv_ssh_plain_packet_payload()` routes registered fds through that
bounded socket-ring packet reader before falling back to Simple framing.

Focused non-live verification after this KEX receive-path update passed:

```bash
cc -fsyntax-only examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl
```

The next focused x64 live gate still failed before auth/exec. OpenSSH continued
to receive the SimpleOS banner and send KEXINIT, but the server stopped in
version exchange:

```text
[sshd-session] version recv bytes len=1157
[sshd-session] invalid client version: nil
```

Detailed serial markers showed `rt_net_recv_version_text()` was entered for the
registered x64 socket fd, then consumed the client identification plus queued
KEXINIT instead of stopping at LF. `rt_net_recv_version_text()` is now capped to
the SSH identification-string limit of 255 bytes and compares numeric LF
(`10`) instead of relying on `'\n'` character-literal comparison.

Focused non-live verification after this version-reader cap passed:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl
cc -fsyntax-only examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c
```

Until the live gate reaches KEX, authentication, and exec-channel success, this
lane cannot claim full "works hosted Linux and SimpleOS" completion. Current
SimpleOS evidence is adapter/preflight/release-plan evidence plus live x64 SSH
version-exchange evidence.

## 2026-06-17 x64 Version-Read ABI Limit Follow-Up

One focused live gate after the Simple-side version-reader cap still failed
before auth/exec:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh artifacts at `build/os/x64-ssh-live.serial.log` and
`build/os/x64-ssh-live.openssh-good.txt` show OpenSSH still receives the
SimpleOS banner and sends KEXINIT, but the server still rejects during client
version receive:

```text
[sshd-session] version recv bytes len=257
[sshd-session] invalid client version: nil
debug1: Remote protocol version 2.0, remote software version SimpleOS_1.0
debug1: SSH2_MSG_KEXINIT sent
Connection closed by 127.0.0.1 port 2222
```

The remaining bounded issue is at the x86_64 C host-access bridge: the direct
TCP `rt_net_recv_bytes()` path compared `avail` against the raw Simple ABI
`max_len`. It now normalizes `max_len` with `simpleos_expose_runtime_value()`,
clamps it to `1..4096`, and applies the normalized limit before consuming the
socket receive ring. This should make `rt_boot_tcp_read_bytes(1)` consume one
byte per version-reader iteration instead of draining a larger chunk.

No second live QEMU gate was run after this fix in this continuation.

## 2026-06-17 x64 Version-Read LF Follow-Up

One focused live gate after the x64 `max_len` normalization still failed before
auth/exec:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh serial evidence shows the C boundary fix worked: reads from the x64 TCP
ring are now one byte at a time, including CR and LF:

```text
[tcp-recv] read 1 bytes from fd=1 first-bytes=0xd
[tcp-recv] read 1 bytes from fd=1 first-bytes=0xa
```

The remaining failure is that the Simple `rt_net_recv_version_text()` loop did
not break on the `0xa` byte and kept draining the following KEXINIT bytes. The
OpenSSH transcripts still show the client receives the SimpleOS banner and sends
KEXINIT, then the connection closes before auth/exec.

The bounded follow-up fix routes registered facade fds through
`rt_boot_tcp_take_version_text(entry.os_fd)`. On x86_64 that host-access helper
already stops at LF and strips CR without consuming KEXINIT. The Simple SSH
protocol validation boundary remains intact: `rt_net_recv_version_bytes()`
reconstructs CRLF bytes from the returned text, and `ssh_extract_version_bytes()`
continues to validate the SSH identification string in Simple.

No second live QEMU gate was run after this fix in this continuation.

## 2026-06-17 x64 Reconstructed Version Bytes Follow-Up

One focused live gate after the registered-fd line-helper route still failed
before KEX/auth/exec:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh serial evidence shows the x86_64 line helper now reads the client
identification correctly and does not drain KEXINIT:

```text
[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[rt-net] version recv entry helper done text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[sshd-session] version recv bytes len=43
[sshd-session] invalid client version: nil
```

The remaining bounded issue is the Simple reconstruction of CRLF-terminated
bytes from the C-returned text. `_rt_net_ascii_text_to_bytes_with_crlf()` now
uses the repo's established text-to-byte pattern,
`line.char_at(i).to_i64() & 0xFF`, before `to_u8()` instead of
`line.byte_at(i).to_u8()`. This keeps protocol validation in Simple while
targeting the parser mismatch on an otherwise correct OpenSSH identification
line.

No second live QEMU gate was run after this fix in this continuation.

## 2026-06-17 x64 Version Result-State Follow-Up

One focused live gate after the reconstructed-version-byte fix still failed
before KEX/auth/exec:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh serial evidence remained:

```text
[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[rt-net] version recv entry helper done text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[sshd-session] version recv bytes len=43
[sshd-session] invalid client version: nil
```

The length is now consistent with a valid OpenSSH identification line: 41 bytes
of text plus CRLF equals 43 bytes. The `nil` error payload points at the
Result-state branch, not at missing version bytes. The bounded follow-up fix in
`src/os/apps/sshd/ssh_session.spl` switches the version parse guard from
`parsed_client_version.is_err()` to `not parsed_client_version.is_ok()` before
calling `unwrap()`, matching the passing `ssh_transport_spec.spl` style for
version parsing.

No second live QEMU gate was run after this fix in this continuation.

## 2026-06-17 x64 Text-First Version Validation Follow-Up

One focused live gate after the Result-state guard fix still failed before
KEX/auth/exec:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

The evidence did not move past version exchange:

```text
[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[rt-net] version recv entry helper done text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16
[sshd-session] version recv bytes len=43
[sshd-session] invalid client version: nil
```

OpenSSH still receives the SimpleOS banner and sends KEXINIT, but the server
closes before KEX payload handling. The bounded follow-up fix moves the live
version receive path in `SshSession.do_version_exchange()` to text-first Simple
validation: it reads `rt_net_recv_version_text()`, checks
`client_version_text.starts_with("SSH-2.0-")`, stores the text as
`self.client_version`, and builds transcript bytes with `ssh_ascii_text_to_bytes()`.
This keeps protocol validation in Simple while avoiding the live SimpleOS
byte-array/Result path that rejects the correct OpenSSH identification line with
a nil error.

No second live QEMU gate was run after this fix in this continuation.

## 2026-06-17 x64 Plain KEXINIT Send Bridge Follow-Up

One focused live gate after the text-first version validation fix still failed
before auth/exec, but it progressed past version exchange and KEXINIT
negotiation:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh serial evidence:

```text
[sshd-session] version exchange ok
[sshd-session] server kexinit len=190
[sshd-session] live plain kexinit rc=0
[tcp-ssh-plain] payload-len=1098 first-byte=0x14
[sshd-session] negotiated kex=curve25519-sha256 hostkey=ssh-ed25519 c2s=aes256-gcm@openssh.com s2c=aes256-gcm@openssh.com
[rt-net] plain recv header len=0
[sshd-session] client ecdh init missing
[sshd-session] disconnect reason=2 desc=no KEX_ECDH_INIT
```

OpenSSH now receives the SimpleOS banner and sends KEXINIT. The server receives
and parses that KEXINIT, then negotiates the expected live OpenSSH profile. The
new bounded failure is that the server KEXINIT send path returned `rc=0`, so
OpenSSH did not proceed with ECDH_INIT.

The bounded follow-up fix adds the missing x86_64
`rt_boot_tcp_send_plain_payload()` bridge in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`. It resolves
synthetic/session fds to the active x64 TCP socket when needed, wraps the Simple
payload in an SSH plaintext packet with padding, sends through
`rt_net_send_bytes()`, and logs `[btcp-x64] send plain payload fd=... rc=...`.

No second live QEMU gate was run after this fix in this continuation.

## Required Follow-Up

1. Continue from `doc/03_plan/os/simpleos/live_gate_vm_decrypt_fail_recovery_2026-06-17.md`.
2. Keep the investigation scoped to `src/os/ssh_qemu_contract.spl`,
   `src/os/qemu_runner_part5.spl`, `src/os/apps/sshd/ssh_session.spl`, and SSH
   daemon socket receive/send wrappers.
3. Run at most one focused live gate per recovery session:
   `test/03_system/os/ssh_live_login_in_qemu_spec.spl`.
4. After live SSH version exchange is proven, add or refresh this lane's
   SimpleOS live evidence before marking `PURE_SIMPLE_SSH_HTTPS_SERVERS_2026_06_17`
   done.

## 2026-06-17 x64 Pure Ed25519 KEX Reply Follow-Up

One focused live gate after adding the x64 plaintext-payload send bridge still
failed before auth/exec, but it progressed through KEX reply and NEWKEYS:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh evidence:

```text
[sshd-session] host ed25519 sign pure len=64
[sshd-session] sig blob len=83
[sshd-session] send_packet msg_type=31 force_plain=1
debug3: receive packet: type 31
debug1: SSH2_MSG_KEX_ECDH_REPLY received
[sshd-session] live c newkeys rc=0
[sshd-session] newkeys sent
[sshd-session] disconnect reason=2 desc=kdf alpha mismatch
```

The bounded fix in `src/os/apps/sshd/ssh_session_kex.spl` routes live Ed25519
host-key signing through the pure Simple signer with
`dual_backend_normal_pure_simple_mode()`. The previous live path ran the runtime
SHA512/signing backend, observed invalid runtime SHA512 lengths, generated a
mismatched runtime signature, and cleared the valid pure Simple signature before
sending the KEX reply.

The remaining blocker is now KDF parity on the live x64 path: server/client key
derivation reaches alpha comparison after NEWKEYS and disconnects with
`kdf alpha mismatch`. The next bounded session should inspect the KDF alpha
inputs/outputs in `src/os/apps/sshd/ssh_session_kex.spl` and related SHA256/KDF
helpers, then run at most one focused live gate.

## 2026-06-17 x64 Pure KDF Follow-Up

One focused live gate after selecting the pure Simple KDF output still failed:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh server-side evidence:

```text
[sshd-session] kdf normal pure selected
[sshd-session] stored key lengths iv_c2s=12 iv_s2c=12 key_c2s=32 key_s2c=32
[sshd-session] send_packet msg_type=7 force_plain=0 active=1 encrypted_io=1
[sshd-session] send_packet branch=encrypted
```

OpenSSH's authoritative failure is before encrypted auth:

```text
debug3: receive packet: type 31
debug1: SSH2_MSG_KEX_ECDH_REPLY received
ssh_dispatch_run_fatal: Connection to 127.0.0.1 port 2222: incorrect signature
```

The bounded fix in `src/os/apps/sshd/ssh_session_kex.spl` removes the runtime
SHA256 KDF veto for the live OpenSSH profile and keeps the pure Simple
`ssh_derive_keys()` output, matching this lane's requirement that runtime/SFFI
is host access only unless the OS provides the primitive as access.

The remaining blocker is now live KEX signature correctness. The next bounded
session should inspect the exchange-hash inputs used by
`_live_exchange_hash_fast()` against the host-key blob and transcript bytes
signed by `ed25519_sign_live_pure_only()`, then run at most one focused live
gate.

## 2026-06-17 x64 Pure Exchange-Hash Follow-Up

One focused live gate after switching live KEX to the pure Simple exchange-hash
helper still failed:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh evidence:

```text
[sshd-session] exchange hash=177e1b5208042edb3664440b72a4e3a9cd81c307ea625bb858ac5e3a2fb89a74
[sshd-session] host ed25519 sign pure len=64
[sshd-session] sig blob len=83
[sshd-session] kdf normal pure selected
debug3: receive packet: type 31
debug1: SSH2_MSG_KEX_ECDH_REPLY received
ssh_dispatch_run_fatal: Connection to 127.0.0.1 port 2222: incorrect signature
```

The bounded fix removed the live-only `rt_tls13_sha256` exchange-hash path:
`src/os/apps/sshd/ssh_session_kex.spl` now uses
`ssh_kex_compute_exchange_hash()` for live and hosted KEX. This aligns the live
signature hash with the pure Simple protocol path and with the earlier pure KDF
selection.

The remaining blocker is still OpenSSH KEX signature verification. Since the
failure persists after pure exchange-hash selection, the next bounded session
should inspect the exact transcript contents included in `I_C`/`I_S`, verify the
advertised host-key blob public key matches the signing public key, and add live
self-verification evidence for `ed25519_verify(stable_pub, exchange_hash,
sig_raw)` before sending the KEX reply.

## 2026-06-17 x64 Ed25519 Self-Verify Follow-Up

One focused live gate after switching live KEX signing to the RFC-self-tested
pure `ed25519_sign()` helper and adding live self-verification still failed:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Fresh evidence:

```text
[sshd-session] exchange hash=6ec5199a43c72311079cfe69d1bca656b527cf01d9cb01b91a8c78b3934f9370
[sshd-session] host ed25519 sign pure len=64
[sshd-session] host ed25519 sig raw=82ed0da1b186d080bc63f8041061cee983c56f3729fdb5b3b80f5e8735d9cc159b9310ca11e7a09dc3098bf49cade8ca1ad548637ac615e4370ae7f961462e06
[sshd-session] live sig self-verify rc=0
[sshd-session] disconnect reason=2 desc=host key self-verify failed
debug3: receive packet: type 1
Received disconnect from 127.0.0.1 port 2222:2:
```

The bounded fix in `src/os/apps/sshd/ssh_session_kex.spl` now refuses to send an
invalid host-key signature. The blocker is narrower than OpenSSH's earlier
`incorrect signature`: pure Ed25519 sign/verify disagree on the live x64 path
for the pinned RFC 8032 key and dynamic exchange hash. The next bounded session
should isolate whether the live failure is in `ed25519_sign()`,
`ed25519_verify()`, or a lower scalar/point helper under native x64, using the
existing RFC 8032 self-test vectors before attempting another live KEX reply.
