# SCV storage publication failures

Source: `test/03_system/app/scv/feature/scv_storage_publication_spec.spl`.
Requirements: `REQ-SCVN-B03-READ`, `REQ-SCVN-B03-PUBLISH`.
Status: authored manual; execution, SPipe generation and maintenance scan
**not_run** because this lane has no qualified native runtime. This document
does not claim passing evidence or replace the generated-manual admission gate.

| Scenario | Setup and operation | Independent evidence required |
|---|---|---|
| Chunk staging fails | Initialize a real repository, create `abc`, block its known SHA-256 chunk staging path with a directory, request a snapshot. | Error outcome; prior head/workspace bytes unchanged; final chunk absent. |
| WAL staging fails | Initialize a repository, create `abc`, block `journal/wal.log.tmp`, request a snapshot. | WAL-begin error; head/workspace bytes unchanged. |
| Head staging fails | Block `HEAD_OP.tmp`, then request a snapshot. | Head-publication error; head/workspace bytes unchanged; pending WAL has neither COMMIT nor ABORT. |
| Workspace staging and recovery fail | Block `workspaces.sdn.tmp`, request a snapshot, then request WAL recovery. | Both operations return errors; head advances but workspace retains its old bytes; WAL remains pending. |

Each scenario uses the `setup`, `capture`, `exercise`, `evidence`, `assert`
steps. Fixture, frozen subject, operation and evidence helpers are implemented
in the executable source. No scenario uses a placeholder passing oracle.

Per-file file-sync/rename does not establish directory-fsync durability or an
atomic transaction across the head, workspace, change records and status index.
Crash/power-loss execution and the full SCVN-B03 acceptance remain pending.
