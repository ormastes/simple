# Feature: live_gate_vm_decrypt_fail_recovery

## Raw Request
$sp_dev doc/03_plan/os/simpleos/live_gate_vm_decrypt_fail_recovery_2026-06-17.md

## Task Type
bug

## Refined Goal
Recover the x64 SSH live QEMU gate by fixing or concretely reclassifying the current pre-KEX banner/version exchange failure without resuming crashed rollout `019e9a76-8773-75e3-affc-721bace4fa25`.

## Acceptance Criteria
- AC-1: The recovery work starts from `doc/03_plan/os/simpleos/live_gate_vm_decrypt_fail_recovery_2026-06-17.md` and `doc/08_tracking/bug/live_gate_vm_decrypt_fail_blocker_2026-06-17.md`, not from the crashed rollout context.
- AC-2: The investigation is scoped to the x64 SSH live QEMU/server version-exchange path, including `src/os/ssh_qemu_contract.spl`, `src/os/qemu_runner_part5.spl`, `src/os/apps/sshd/ssh_session.spl`, and the SSH daemon socket receive/send wrappers.
- AC-3: The next implementation pass either fixes one local cause of the accepted-connection/zero-byte-version-read failure or updates `doc/08_tracking/bug/live_gate_vm_decrypt_fail_blocker_2026-06-17.md` with the next concrete blocker and evidence.
- AC-4: Verification runs at most one focused gate command for this lane in a session, using `test/03_system/os/ssh_live_login_in_qemu_spec.spl`, and records the result and artifact paths.
- AC-5: The lane does not chase AES-GCM decrypt behavior until a fresh focused run reaches encrypted packet receive or logs a fresh `recv decrypt fail aes256-gcm` marker.
- AC-6: The work does not modify unrelated dirty files from other active lanes.

## Scope Exclusions
- Do not resume rollout `019e9a76-8773-75e3-affc-721bace4fa25`.
- Do not run repeated live gates in one session.
- Do not fold unrelated GPU, database, browser, office, or web hardening work into this lane.
- Do not treat the stale decrypt-fail label as authoritative without fresh encrypted-packet evidence.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: bug).
