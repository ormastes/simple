# BUG: x86_64 sshd fails SSH version exchange under freestanding native-build

**Status:** open
**Severity:** high (blocks all x86_64 SSH login; rv64 SSH login is proven, x64 is not)
**Component:** sshd version exchange / net recv facade under freestanding native-build
**Found:** 2026-07-08, booting a merged ring-3 + sshd x86_64 kernel

## Symptom

A real host `ssh -p 2222 root@127.0.0.1 true` connects to the in-guest x86_64
sshd, the TCP connection is accepted and the server banner is sent, the client
version IS received correctly C-side, but the server then reads an EMPTY client
version and aborts:

```
[tcp] Connection established on port 22
[sshd] accepted client fd=200
[sshd-session] version banner send rc=22
[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1 Ubuntu-3ubuntu13.16   <- correct C-side
[sshd-session] version raw bytes len=41 hex=57579a5757575757...     <- GARBAGE (Simple-side)
[rt-net] version recv raw-fast
[rt-net] version recv raw-fast done text=                            <- EMPTY
[sshd-session] version recv text=
[sshd-session] invalid client version text=
[sshd-session] run stop version_exchange
```

QEMU serial: `build/os/x64-ssh-ring3.serial.log` from the boot of
`build/os/simpleos_ssh_ring3.elf`.

## Analysis

Two freestanding-native-build issues in the version-exchange path:

1. **Double-take consumes the buffered version.** `rt_net_recv_version_bytes`
   (`src/os/kernel/net/rt_net_socket_facade.spl:366`) calls
   `rt_boot_tcp_take_version_bytes(fd)` (extern, L18) which appears to CONSUME the
   buffered version; the subsequent `rt_net_recv_version_text` (L326) →
   `rt_boot_tcp_take_version_text(fd)` (L17) then returns empty. The session
   (`src/os/apps/sshd/ssh_session.spl`) takes both, so whichever runs second gets
   nothing. Either the C "take" must be non-consuming (return the same buffer), or
   the session must take exactly once and derive both text+bytes from it.
2. **`[u8]` read-back is boxed.** The Simple-side hex dump of the 41 received bytes
   (`version raw bytes … hex=5757…`) is garbage while the C-side text is correct —
   the boxed-`[u8]` stride-1 read hazard (same class fixed in
   `x86_64_fs_exec_ring3.spl` via `rt_bytes_u8_at`/mmio and in the loader frame via
   `.to_u64()`-boxing). Any `arr[i]` over the received `[u8]` reads garbage; use
   `rt_bytes_u8_at` / the C helpers consistently.

Why rv64 passes and x64 does not: rv64 is the proven SSH lane with durable serial
transcripts (`build/os/rv64-ssh-live.serial.log`); the x64 ssh_live spec has never
produced passing evidence (`doc/08_tracking/test/test_result.md` shows 100%
failure). The freestanding `[u8]`/take semantics differ on the x64 codegen path.

## Repro

Build + boot the merged kernel (proven to build, boot, and reach the sshd accept
loop AFTER vmm_init — net survives vmm):
`examples/09_embedded/simple_os/arch/x86_64/ssh_ring3_entry.spl`, native-build to
`build/os/simpleos_ssh_ring3.elf` (see
`doc/05_design/os/ssh/simpleos_ssh_ring3_exec_plan.md`), boot under QEMU q35 with
`-netdev user,hostfwd=tcp::2222-:22 -device virtio-net-pci` + an NVMe disk, then
`ssh -p 2222 root@127.0.0.1 true` (password `simpleos`).

## Impact

This is the gate for "hello world over SSH" on x86_64: the ring-3 FS-exec path and
the merged kernel (nvme+vmm+net+sshd, net survives vmm) are proven; SSH LOGIN must
work before an SSH command can drive `fs_exec_spawn_ring3`. Fixing the version
exchange (then verifying KEX/packet/auth for the same `[u8]`/take hazards) makes
x64 SSH login work; the remaining exec wiring is small (route the resolved path to
`fs_exec_spawn_ring3`).
