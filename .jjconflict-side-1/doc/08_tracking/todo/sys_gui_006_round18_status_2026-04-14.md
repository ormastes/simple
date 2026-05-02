# SYS-GUI-006 — Round 18 Status (2026-04-14)

## TL;DR

- **NOT LIVE-GREEN.** Two blockers remain; neither is harness-level.
- **Blocker A (new, hard-stop):** Interpreter-mode "unknown extern" for
  `rt_fd_write`. The four unix-socket fd externs declared in
  `src/runtime/platform/unix_common.h` and used in
  `src/lib/nogc_sync_mut/qemu/qmp_client.spl` are **not registered** in
  `src/compiler_rust/compiler/src/interpreter_extern/`. The network/ module
  only contains `http.rs`, `tcp.rs`, `udp.rs` — no unix-socket/fd module.
  Because the spec runs in interpreter mode, execution halts with
  `semantic: unknown extern function: rt_fd_write` before QEMU is ever
  launched.
- **Blocker B (carried from Round 16):** Kernel ELF
  `build/os/simpleos_desktop_e2e_32.elf` is not built in this workspace,
  and `qemu-system-x86_64` is not available on this host. Even if Blocker A
  were fixed, the live QEMU lane cannot run here.

## Test Run Evidence

Command:
```
/home/ormastes/dev/pub/simple/bin/simple test \
  test/system/simpleos_desktop_framebuffer_spec.spl
```

Output (tail):
```
SKIP: Kernel not built: build/os/simpleos_desktop_e2e_32.elf
[simpleos_desktop_fb_spec] qemu-system-x86_64 not available, skipping live capture
[simpleos_desktop_fb_spec] R13 pre-wait sleep for serial-log flush
[simpleos_desktop_fb_spec] desktop paint-ready marker not seen within 180s
  ✗ boots desktop, captures framebuffer via QMP, and matches baseline
    semantic: unknown extern function: rt_fd_write
  ✓ has a baseline directory for simpleos_desktop_framebuffer captures

3 examples, 2 failures
FAILED (2506ms)
```

## Extern Registration Gap (Blocker A — Root Cause + WIP Fix Status)

The four externs required by `qmp_client.spl`:

| Extern | Defined in runtime.h | Implemented in unix_common.h | Registered in interpreter_extern/ |
|--------|---------------------|------------------------------|-----------------------------------|
| `rt_unix_socket_connect` | ✓ line 379 | ✓ line 591 | WIP (not compiled) |
| `rt_fd_write` | ✓ line 380 | ✓ line 610 | WIP (not compiled) |
| `rt_fd_read_until` | ✓ line 381 | ✓ line 619 | WIP (not compiled) |
| `rt_fd_close` | ✓ line 382 | ✓ line 637 | WIP (not compiled) |

**WIP fix is written but not yet compiled into the binary.**
`src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs` exists in
this workspace with full implementations of all four functions using
`std::os::unix::net::UnixStream` and a `Mutex<ConnTable>`. It is wired into
`mod.rs` (line 93: `pub mod qmp_socket;`, lines 791–794: dispatch arms).

However, `bin/simple` is a symlink to
`/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple` —
the pre-built bootstrap binary from the **main workspace**, not rebuilt from
these WIP sources. The test therefore ran against the old binary and hit
`semantic: unknown extern function: rt_fd_write`.

**Fix needed for Round 19:** Run `bin/simple build` in the workspace (or
rebuild the Rust compiler crate) so the WIP `qmp_socket.rs` registration is
compiled into the binary before the test is re-run.

## Context Preamble Claims vs. Reality

The Round-18 task brief mentioned fixes `pulwy 8e24` (NVMe guard — skip
`launcher_shortcut_dispatch` when NVMe absent) and `pywp 46b3` (QMP
persistent unix-socket fd). Investigation findings:

- **`pywp 46b3` (QMP persistent fd):** LANDED. `qmp_client.spl` correctly
  keeps a persistent fd open for the session (lines 4–101).
- **`pulwy 8e24` (NVMe guard):** NOT VISIBLE in this workspace.
  `shell.spl` line 587 calls `launcher_shortcut_dispatch` unconditionally.
  `launcher.spl` `_dispatch_seeded_shortcut` does not guard on NVMe presence.
  Either the fix targets a different code path not examined, or it has not
  landed in this workspace snapshot.
- **Interpreter extern registration:** Not mentioned in any prior round status.
  This is a newly-surfaced blocker.

## Spec Results Summary

| Example | Round 18 |
|---------|----------|
| builds desktop_e2e_entry | SKIP (kernel not built) |
| boots desktop, captures framebuffer | ✗ FAIL (unknown extern rt_fd_write) |
| has a baseline directory | ✓ PASS |
| **Total** | 1 passed, 2 failed |

## Status: NOT LIVE-GREEN

## Required Fixes (Round 19)

1. **[Build] Rebuild the compiler binary** from the workspace sources so the
   WIP `qmp_socket.rs` registration compiles in. Run `bin/simple build` (or
   `cargo build` in `src/compiler_rust/`) before re-running the spec. The code
   is already written — only the binary needs to catch up.
2. **[Build environment]** Ensure `build/os/simpleos_desktop_e2e_32.elf` is
   present and `qemu-system-x86_64` is available in the Round-19 workspace for
   an actual live QEMU run and capture.
3. **[Verify]** Confirm `pulwy 8e24` NVMe guard is present in `launcher.spl`
   or `shell.spl` — it was not found in this workspace snapshot. `shell.spl`
   line 587 calls `launcher_shortcut_dispatch` unconditionally with no NVMe
   guard.

## Next Steps

Pass to Round-19 with:
- Action 1: rebuild binary from WIP sources (qmp_socket.rs fix already written).
- Action 2: live QEMU run requires kernel ELF build + qemu-system-x86_64.
- Action 3: verify NVMe guard landing.
