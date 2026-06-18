# Live Gate VM Decrypt-Fail Blocker - 2026-06-17

## Scope

Lane: `live gate / VM decrypt-fail`

Fresh session recovery for crashed rollout `019e9a76-8773-75e3-affc-721bace4fa25`.

## Focused Gate Run

Command run once:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after ~63s.

Evidence:

- `build/os/ssh_live_login_fresh_2026-06-17.log`
- `build/os/x64-ssh-live.serial.log`
- `build/os/x64-ssh-live.openssh-good.txt`
- `build/os/x64-ssh-live.openssh-bad-auth.txt`

## Observed Failure

The fresh failure did not reach the AES-GCM decrypt path.

OpenSSH connects to `127.0.0.1:2222`, emits its local version string, then fails with:

```text
Connection timed out during banner exchange
Connection to 127.0.0.1 port 2222 timed out
```

The guest serial log repeats:

```text
[sshd-session] version recv bytes len=0
[sshd-session] disconnect reason=2 desc=no KEXINIT received
```

No fresh `recv decrypt fail aes256-gcm` marker was observed in the focused run.

## Blocker

The current live-gate failure is a pre-KEX banner/version exchange failure, not a confirmed VM decrypt failure. A decrypt-path fix would be speculative until the live gate reaches encrypted packet receive again.

Next bounded step: debug why the x64 SSH guest accepts the host connection but the server-side version reader sees EOF/zero bytes before receiving the OpenSSH client identification string.

## 2026-06-17 Follow-Up

The next focused inspection found the live failure was more specific than a
generic zero-byte banner read. The fresh serial log showed:

```text
[sshd] accepted client fd=0
[rt-net] version bytes recv fn sock_fd=0
[rt-net] version bytes recv branch=nil
[sshd-session] version recv bytes len=0
[sshd-session] invalid client version: nil
```

Root cause identified: `SshDaemon.accept_loop()` accepted clients through the
raw `rt_boot_tcp_accept_timeout()` path, but `SshSession` reads through
`rt_net_socket_facade`. A raw accepted fd of `0` was never registered in the
facade socket table, so `rt_net_recv_version_bytes(0)` could not resolve the
underlying OS fd.

Bounded fix applied: `src/os/apps/sshd/sshd.spl` now creates, binds, listens,
accepts, and closes through `rt_net_socket_facade` (`rt_net_socket`,
`rt_net_bind_and_listen`, `rt_net_accept`, `rt_net_close`) so accepted client
fds are registered before session reads.

Focused non-live gate:

```bash
bin/simple check src/os/apps/sshd/sshd.spl src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl
```

Result: PASS for all 3 files.

Status remains open until a subsequent bounded live QEMU gate proves the SSH
version exchange progresses past the registered-fd path.

## 2026-06-17 Registered-Fd Follow-Up

One subsequent focused live gate was run after the fd-facade fix:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 59s.

Progression evidence:

```text
[sshd] accepted client fd=1001
[rt-net] version bytes recv fn sock_fd=1001
[rt-net] version bytes recv branch=entry os_fd=0
[sshd-session] version recv bytes len=1153202240580805315
```

The fd registration blocker is no longer the current failure: the session now
uses facade fd `1001` and resolves it to accepted OS fd `0`. The new bounded
failure is the accepted-fd byte-array helper: `rt_boot_tcp_take_version_bytes`
is valid only on the legacy raw fd `200` path and returns a corrupt array length
when called through the registered accepted fd path.

Bounded fix applied: `rt_net_recv_version_bytes()` now keeps
`rt_boot_tcp_take_version_bytes()` only for the raw fd `200` fast path. For
registered facade fds it reads the version line through the stable
`rt_net_recv_version_text()` path and reconstructs CRLF-terminated ASCII bytes
in Simple before `ssh_extract_version_bytes()`.

Focused non-live gate:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

Result: PASS for all 3 files.

Status remains open until the next bounded live QEMU gate proves whether this
version-byte fix reaches KEX/decrypt.

## 2026-06-17 Active-Client Handle Follow-Up

One focused live gate was run after the version-byte facade fix:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 58s.

Fresh evidence:

```text
[sshd] accepted client fd=1001
[sshd-session] raw_send len=22
[rt-net] send fn sock_fd=1001 len=22
[rt-net] version bytes recv fn sock_fd=1001
[rt-net] version bytes recv branch=entry os_fd=0
[rt-net] version recv fn sock_fd=1001
[rt-net] version recv branch=entry os_fd=0
```

OpenSSH still timed out during banner exchange, which means the server banner
send did not reach the client. Runtime inspection showed the boot TCP helpers
use listener handle `100` and active-client handle `200`; accepted facade fd
`1001` was storing `os_fd=0`, so `rt_boot_tcp_write_bytes(0, ...)` was rejected
by the runtime.

Bounded fix applied: `rt_net_accept()` now keeps the synthetic facade fd for
Simple callers but stores runtime active-client handle `200` in the socket table
after `rt_boot_tcp_accept_timeout()` succeeds. This makes facade send/read/close
paths call the boot TCP helpers with the handle they support.

Focused non-live gate:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/sshd.spl src/os/apps/sshd/ssh_session.spl
```

Result: PASS for all 3 files.

Status remains open until a later bounded live QEMU gate proves whether the
active-client handle mapping reaches SSH version exchange and KEX/decrypt.

## 2026-06-17 Facade Banner Send Follow-Up

One focused live gate was run after the accepted-handle mapping fix:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 58s.

Fresh evidence:

```text
[sshd] accepted client fd=1001
[sshd-session] raw_send len=22
[rt-net] send fn sock_fd=1001 len=22
[rt-net] version bytes recv fn sock_fd=1001
[rt-net] version bytes recv branch=entry os_fd=200
[rt-net] version recv fn sock_fd=1001
[rt-net] version recv branch=entry os_fd=200
```

The accepted-handle mapping is now active in the live image (`os_fd=200`), but
OpenSSH still timed out during banner exchange. The session was still sending
the server identification string through byte-array `rt_net_send_bytes()` for
synthetic facade fd `1001`, and that path did not log a return code for entry
sends. The runtime already has a dedicated boot TCP SSH banner helper for active
client handle `200`.

Bounded fix applied: `rt_net_socket_facade` now exposes
`rt_net_send_ssh_banner(sock_fd)`, resolving synthetic facade fds through the
socket table before calling the boot TCP banner helper. `SshSession` now uses
that facade method for version-exchange banner send, keeping the direct runtime
call out of the session and avoiding byte-array marshalling during the SSH
identification exchange.

Focused non-live gate:

```bash
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

Result: PASS for all 3 files.

Status remains open until a later bounded live QEMU gate proves whether facade
banner send reaches OpenSSH and advances to KEX/decrypt.

## 2026-06-17 TCP Handshake Readiness Follow-Up

One focused live gate was run after the facade banner-send fix:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 60s.

Fresh evidence:

```text
[sshd-session] version banner send start
[rt-net] banner send fn sock_fd=1001
[rt-net] banner send entry rc=0
[sshd-session] version banner send rc=0
[rt-net] version bytes recv branch=entry os_fd=200
```

OpenSSH still timed out during banner exchange. The facade banner helper now
returns through the registered active-client handle, so the next concrete issue
is lower in the boot TCP connection timing. The boot TCP accept loop could
previously return after a SYN-only poll-count fallback before seeing the
client's final ACK or payload, allowing SSHD to send the identification banner
before the TCP connection was fully established from the client's point of view.

Bounded fix applied: `rt_boot_tcp_accept_timeout()` no longer returns from the
SYN-only fallback. The TCP processor now marks the client ready on the first
post-SYN ACK or payload, and accept returns only after that readiness marker.

Focused non-live gates:

```bash
cc -fsyntax-only src/os/kernel/arch/riscv64/boot/freestanding_runtime.c
bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/sshd.spl
```

Result: both passed.

Status remains open until a later bounded live QEMU gate proves whether the
handshake-readiness fix lets OpenSSH receive the banner and advances to
KEX/decrypt.
