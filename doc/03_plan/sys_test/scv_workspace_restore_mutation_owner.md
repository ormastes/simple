# SCV Workspace Restore Mutation Owner Test Plan

**Status:** planned, not executable; native owner does not exist. Runtime
qualification is **NOT_RUN**. This plan and the existing authored scenarios
are not test passes.

**Traceability:** `REQ-004` in
[`scv_full_phase2_2026-10-27.md`](../../02_requirements/feature/scv_full_phase2_2026-10-27.md).

The existing restore spec is in
[`scv_restore_spec.spl`](../../../test/03_system/app/scv/feature/scv_restore_spec.spl).
Its preflight sections contain scenarios for read-only validation and the explicit
`mutation=unsupported`; it does not exercise safe publication or recoverable
workspace mutation. The same file also contains a legacy destructive restore
scenario; that scenario does not establish race safety or crash recovery.

## Planned BDD scenarios

These become executable only after a shared retained-root mutation owner and
its injectable crash/concurrency harness exist. A passing source-only or
preflight-only test cannot close any scenario below.

| ID | Scenario | Required observable result |
|---|---|---|
| MUT-01 | Crash after durable intent but before the first rename | Recovery leaves all original entries intact and resumes or reports a durable no-op. |
| MUT-02 | Crash after moving one of several entries but before recording progress | Recovery discovers the quarantine entry by transaction identity, preserves bytes, and reaches a journal-consistent state. |
| MUT-03 | Crash after replacement publication but before progress/final operation record | Recovery recognizes the published entry, does not overwrite it, and completes or reports explicit recovery required. |
| MUT-04 | Concurrent replacement of a target leaf immediately before quarantine rename | The entry actually moved is inspected after the atomic rename; if it is not the expected identity, it remains recoverable in quarantine and no bytes are discarded. |
| MUT-05 | A symlink or directory is swapped into a planned leaf during restore | The raced-in entry is never followed or recursively removed; it remains recoverable and the transaction stops with conflict. |
| MUT-06 | An editor creates a new destination after quarantine but before replacement publication | No-replace publication fails; the editor entry, staged replacement, and quarantine remain accounted for. |
| MUT-07 | Rollback destination is concurrently occupied | No-replace rollback does not overwrite the occupant; the archive remains and recovery-required is reported. |
| MUT-08 | A held descriptor or hard link mutates the quarantined inode after move | The operation detects insufficient immutable evidence, preserves the entry, and never claims archived snapshot bytes are fixed. |
| MUT-09 | Symlink ancestor is swapped after preflight | Descriptor-rooted resolution refuses escape; no outside file is created, read, or changed. |
| MUT-10 | Unsupported host/platform provider | Restore reports unsupported before any workspace or operation metadata mutation. |
| MUT-11 | A parent directory is renamed or replaced after planning | The operation detects the changed path binding; it does not report success for a detached parent, and all moved entries remain recoverable. |
| MUT-12 | A quarantine name is occupied before a move | No-replace quarantine fails without overwriting the existing archive or dropping the source leaf. |
| MUT-13 | Disk-full or directory-fsync failure after a visible move | The result is explicitly uncertain/recovery-required; intent and moved bytes remain inspectable and no cleanup deletes them. |
| MUT-14 | A foreign operation-head change appears before recovery | The common expected-generation authority rejects the stale restore; recovery does not rewind or overwrite the foreign head and preserves workspace/journal evidence. |
| MUT-15 | A transaction request ID is retried with different payload | The owner rejects the mismatch and leaves both existing transaction evidence and workspace bytes unchanged. |
| MUT-16 | Retention/GC runs during an interrupted transaction | Intent, quarantine, staged replacements, before-images, and target closure remain pinned until durable commit or explicit recovery closure. |

Every scenario must compare all affected workspace bytes, transaction journal,
quarantine contents, and operation metadata before and after recovery. Fault
injection must be owned by the native provider test harness, not implemented as
a shell substitute for production mutation.

Missing-provider and unsupported-provider scenarios must call the public
restore/mutation entrypoint and assert that original bytes and operation head
remain unchanged. A capability-status query alone is insufficient. Until that
entrypoint is gated, those scenarios are planned and must not be represented as
passing current executable tests.

## Current executable coverage

The preflight sections contain scenarios for target validation, dirty-path
refusal, corrupt target data, path-shape conflicts, and symlink-parent
preflight. The legacy destructive restore scenario remains; neither it nor the
preflight scenarios establish race safety, durable mutation, or crash
recovery. No runtime tests or documentation generation were run for this
plan.
