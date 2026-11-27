# Capability-manager hardening dropped by stale-snapshot merge (2026-11-15)

Status: FIXED on `work/capability-hardening-restore-20261115`.
Related: `container_detect_and_session_layer_clobbered_2026-11-15.md` (same clobber, session layer).

## Defect
`src/os/kernel/ipc/capability.spl` on release/1.0.0 lost hardening present at `e274cd33719~1`:
1. `check_file_access` ignored capabilities: with no unveil it returned true for any
   path/perm; unknown or empty perms were not rejected.
2. `revoke` / `revoke_transitive` left an emptied set as `is_pledged:false` + zero tokens,
   which is the ambient-full encoding.
3. `init_task` stored an ambient-full set (`CapabilitySet.full()`) for any task; only
   init (task 1) may hold it, others must be clamped to deny-all.
4. `capability_set_from_sandbox_lowering` built FileRead/FileWrite/ProcessSpawn tokens
   without `token_id`/`depth` (no revocation lineage).
5. `_path_starts_with` used raw `starts_with`, so unveil `/data` admitted `/database`.

## Fix
Restored all five from `e274cd33719~1`; `_path_starts_with` additionally accepts a
trailing-slash prefix and compares the boundary as a `char` (ADR-005).

## Specs
- Reproducer + generalization: `test/01_unit/os/security/capability_hardening_restore_spec.spl`
  (9 scenarios). Against the unfixed file 5 fail (prefix boundary, per-perm x2, init_task
  full clamp, sandbox provenance). The two revoke scenarios pass on both, because the
  emptied-set encoding is not observable via `check()` there; they stay as guards.

## Pre-existing failures (unchanged by this fix, still open)
Measured on the same base with the unfixed vs fixed `capability.spl`:
- `test/01_unit/os/kernel/ipc/capability_spec.spl`: 4 failures before, 3 after
  (`revokes a capability token` now passes). Remaining: `initializes a task with empty
  capabilities` (:86, expects task 1 + full() to lack ProcessSpawn, contradicting the
  task-1 init exemption), `grants capability from source to target` (:171), and
  `new tasks get full capability record at spawn` (:421). Needs an owner decision on
  init-task ambient authority.
- `abi_v1_transfer_contract_spec.spl`: 4 failures, `SingleUseLedger` not found.
- `syscall_mmap_spec.spl`: 11 failures, `_handle_sys_mmap` now requires `task_id`.
