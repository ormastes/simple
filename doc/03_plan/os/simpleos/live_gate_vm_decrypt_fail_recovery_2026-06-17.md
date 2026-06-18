# Live Gate VM Decrypt-Fail Recovery Plan - 2026-06-17

## Goal

Continue the crashed rollout lane without resuming rollout
`019e9a76-8773-75e3-affc-721bace4fa25`.

Current target: recover the x64 SSH live QEMU gate by following the fresh
evidence, not the stale decrypt-fail label.

## Current Evidence

Primary blocker:

- `doc/08_tracking/bug/live_gate_vm_decrypt_fail_blocker_2026-06-17.md`

Fresh gate artifacts:

- `build/os/ssh_live_login_fresh_2026-06-17.log`
- `build/os/x64-ssh-live.serial.log`
- `build/os/x64-ssh-live.openssh-good.txt`
- `build/os/x64-ssh-live.openssh-bad-auth.txt`

Focused gate already run once in the recovery session:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl
```

Result: FAIL after about 63 seconds.

## Finding

The fresh failure did not reach the AES-GCM decrypt path.

OpenSSH connected to `127.0.0.1:2222`, emitted its local version string, then
timed out during banner exchange. The guest serial log repeatedly showed:

```text
[sshd-session] version recv bytes len=0
[sshd-session] disconnect reason=2 desc=no KEXINIT received
```

No fresh `recv decrypt fail aes256-gcm` marker was observed.

## Next Bounded Work

1. Inspect only the x64 SSH live QEMU/server version-exchange path:
   - `src/os/ssh_qemu_contract.spl`
   - `src/os/qemu_runner_part5.spl`
   - `src/os/apps/sshd/ssh_session.spl`
   - socket receive/send wrappers used by the SSH daemon in QEMU
2. Determine why the guest accepts the host connection but the server-side
   version reader observes EOF/zero bytes before receiving the OpenSSH client
   identification string.
3. Fix one bounded issue if the cause is local and clear.
4. If the cause is not clear, update
   `doc/08_tracking/bug/live_gate_vm_decrypt_fail_blocker_2026-06-17.md` with
   the next concrete blocker.
5. Run at most one focused gate command, then stop.

## Guardrails

- Do not resume the crashed rollout.
- Do not touch unrelated dirty files.
- Do not chase the decrypt path until the live gate reaches encrypted packet
  receive again.
- Do not run repeated green or failing gates; one focused gate per session is
  enough for this lane.
