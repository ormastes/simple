# Signed pre-helper parent-budget planning

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored manual, not generated execution evidence.

Executable: `test/03_system/app/orchestrator/feature/host_parent_budget_spec.spl`.
Production: `src/lib/nogc_sync_mut/orchestration/host_parent_budget_v1.spl` and the `host-parent-budget` route in `host_local_command_v1.spl`.

HOST-HELPER-04 has five authored scenarios:

1. Real budget grant/approval plus actual retained parent journal publish and load the same canonical record, without a helper packet, native command or journal mutation.
2. Each load rejects a different selected parent, changed scope and approval expiry discovered by the refreshed clock.
3. Forged signatures and late expiry reject before publishing a reference directory.
4. Canonical roundtrip succeeds while extra input, unknown fields and corrupted retained bytes refuse; a new store never overwrites the corrupted evidence.
5. An actual Windows scripted Container owner refuses public store/load before record access until native privacy support exists, while pure retained-parent validation remains independent of this persistence guard.

The fixtures use real cryptographic signatures and filesystem/journal owners with an explicitly unused scripted Container owner. They do not establish native enrollment, Windows privacy, stream permission or quota enforcement. Helper begin remains the separate authorization/admission boundary. Same-budget changed-proof renewal is refused rather than silently replacing evidence.

No SSpec, compiler or platform command ran. Local static tooling uses shared CPU set 0–4.
