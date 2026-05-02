# SSH Live Login Follow-up — 2026-04-26

## Implemented in this pass

- `src/os/apps/sshd/ssh_session.spl`
  - Added a deterministic live fast path for the first `CHANNEL_OPEN("session")` packet.
  - Seeded local channel `0` directly in the Simple-side channel table and sent `CHANNEL_OPEN_CONFIRMATION(recipient=0, sender=0, window=2097152, max_packet=32768)` without depending on the C-side channel table for `local_id = 0`.
  - Added explicit logging for `CHANNEL_REQUEST("exec")`.
  - Added a one-shot `true` exec fast path that returns channel success, `exit-status`, EOF, and CLOSE in-order.
- `src/os/apps/sshd/ssh_channel.spl`
  - Added `seed_open(...)` for deterministic Simple-side channel seeding.
  - Added local-id-0 fallback handling in `find`, `close`, `adjust_window`, `consume_remote_window`, and `consume_local_window`.
- `test/qemu/os/common/qemu_os_harness.spl`
  - Added per-run host-port allocation.
  - Added stale-resource cleanup for the selected host port / qmp socket / serial / stderr paths.
  - Split QEMU stderr capture from the serial log.
  - Switched QEMU spawn to a quoted shell wrapper so stderr redirection is preserved.
- `test/system/ssh_live_login_in_qemu_spec.spl`
  - Switched to per-run host ports and artifact paths.
  - Moved guest teardown ahead of assertions so failures do not leak guests.
  - Persisted failure serial and stderr logs separately.
- `test/system/simpleos_guest_toolchain_live_spec.spl`
  - Switched to per-run host ports and artifact paths.
  - Moved guest teardown ahead of assertion/fail paths.
  - Persisted failure serial and stderr logs separately.
- `src/os/apps/sshd/sshd.spl`
  - Replaced daemon-start serially-visible `log_info` calls with direct serial writes so the live lane no longer traps on baremetal `rt_env_get` before the accept loop.

## Verification

- `bin/simple test test/system/os_ssh_spec.spl`
  - PASS
- `bin/simple test test/system/ssh_live_login_in_qemu_spec.spl`
  - FAIL in the Cranelift lane
  - LLVM lane still skips because the local compiler is not built with the `llvm` feature

## Current blocker after this pass

- The live lane now reaches:
  - TCP accept
  - SSH banner exchange
  - KEX
  - `NEWKEYS`
  - encrypted `SERVICE_REQUEST("ssh-userauth")`
  - encrypted `SERVICE_ACCEPT("ssh-userauth")`
- OpenSSH then aborts before auth continues with:
  - `padding error: need 28 block 16 mod 12`
  - `message authentication code incorrect`
- The retained guest serial log shows the connection closes immediately after the encrypted `SERVICE_ACCEPT` response, so the current verifier blocker is again an encrypted post-`NEWKEYS` framing/MAC issue earlier than the planned session-channel `exec` verification point.
