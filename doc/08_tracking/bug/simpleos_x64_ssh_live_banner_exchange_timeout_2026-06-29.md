# SimpleOS x64 SSH Live Banner Exchange Timeout
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- status: open
- date: 2026-06-29
- lane: SimpleOS hardening / SSH FS exec evidence

## Summary

The x64 live SSH QEMU gate now builds the `ssh_live_entry.spl` guest with the
available release Simple binary, but OpenSSH sessions still time out during
banner exchange before authentication or exec-channel handling.

## Reproduction

```bash
SIMPLE_LIB=src SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple \
  release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --timeout-ms=900000 --clean --format json
```

## Current Evidence

- Build command uses `release/x86_64-unknown-linux-gnu/simple native-build`.
- Native build succeeds for `build/os/simpleos_ssh_live_32.elf`.
- Guest reaches `[sshd] SSH daemon listening on port 22`.
- OpenSSH transcript files end with `Connection timed out during banner exchange`.
- Serial log repeatedly reports `rt-net version recv branch=nil` followed by
  `disconnect reason=2 desc=no KEXINIT received`.
- The hardening matrix remains `7/9`; `executable_launch_from_fs` and
  `ssh_shell_smf_and_exec` stay failed until authenticated sessions can reach
  `SESSION OK shell ...` transcript output.

## Touched Follow-Up Surface

The host probe now asks for durable session transcripts:

- `build/os/x64-ssh-live.session-smf.txt`
- `build/os/x64-ssh-live.session-exec.txt`

The SSH exec bridge has a focused Simple launch proof path for
`simple.smf --version` and `simple --check`, but live OpenSSH does not reach it
while banner exchange fails.

## BF-9 Update (2026-11-26) — fix implemented, verify waiting (`fix-implemented-verification-pending`)

- **Root causes fixed**:
  1. `src/os/apps/sshd/sshd.spl`: Switched `@cfg(not(riscv64))` listener helpers to `@when(riscv64): ... @elif((baremetal or simpleos) and x86_64): ... @else: ...` so x86_64 baremetal binds/listens/accepts/closes via VirtIO-net `rt_net_socket`/`rt_net_bind`/`rt_net_listen`/`rt_net_accept`/`rt_net_close` (decoded cleanly without `NOP2` `rt_io_tcp_*` stubs and preserving raw fd `0` rather than rewriting `0 -> 200` via RV64 `normalize_boot_tcp_client_fd`), while host `--mode=interpreter` retains `rt_io_tcp_*`.
  2. `src/os/kernel/net/rt_net_socket_facade.spl`: Guarded C-colliding `@export("C")` exports (`rt_net_socket`, `rt_net_bind`, `rt_net_listen`, `rt_net_accept`, `rt_net_close`, `rt_net_send_bytes`, `rt_net_recv_bytes`, `rt_net_recv_version_text`, `rt_net_recv_ssh_plain_packet_payload`, `rt_net_bind_and_listen`) with `@when(not((baremetal or simpleos) and x86_64)):` so Simple no longer shadows `baremetal_stubs.c`'s VirtIO-net symbols (`[rt-net] version recv branch=nil` eliminated), and implemented `@else:` x86_64 baremetal `rt_net_send_ssh_banner`, `rt_net_recv_version_bytes`, and `rt_net_recv_ssh_encrypted_packet` over `rt_net_send_bytes` / `rt_net_recv_bytes`. Also fixed `_rt_net_trim_crlf` to check `10u32`/`13u32` instead of raw `'\n'`/`'\r'`.
- **Host spec**: `SIMPLE_LIB=src bin/simple test test/01_unit/os/kernel_bf9/bf9_x64_ssh_banner_facade_spec.spl --mode=interpreter` -> `4 examples, 0 failures`.
- **QEMU/baremetal verification pending**:
  ```sh
  sh scripts/os/ssh_multi_cmd.shs
  ```

