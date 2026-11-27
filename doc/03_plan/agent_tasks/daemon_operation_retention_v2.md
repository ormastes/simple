# DAE-05 bounded delivery and file ownership

Status: R3 design only; independent Astra review required before implementation.
Root allocated `/home/yoon/dev/simple-collected-stream-null-20261114`, branch
`work/daemon-retention-design-20261115`, exclusively for this lane. No commit,
push, runtime effect or new worktree is authorized by this design assignment.

| Responsibility | Owner |
| --- | --- |
| Concrete API/storage/retention design | Astra DAE-05 lane |
| Independent design acceptance | Root-appointed independent Astra reviewer |
| Optional bounded implementation worker | One Sol worker, only after interface freeze and ownership approval; currently N/A |
| Final source/manual review | Independent Astra reviewer |
| Integration, merge and release admission | Root; no lane-side publication |
| Runtime/platform qualification | Future authorized run; currently NOT_RUN |

Design-owned files are this plan,
`doc/03_plan/sys_test/daemon_operation_retention_v2.md`, and
`doc/05_design/daemon_operation_retention_v2.md`. Do not edit shared main, Host,
Windows, Caret or another worktree, or the frozen Host index.

Proposed Slice A source ownership, subject to root approval:

- Extend `src/lib/common/task_runner/distributed_operation_journal_v2.spl`.
- Add `src/lib/common/task_runner/distributed_operation_checkpoint_v2.spl` for
  strict checkpoint SDN encoding/decoding and paging.
- Add `src/lib/common/contracts/distributed_operation_retention_v2.spl` for
  the explicit retention profile;
  propagate its optional value through existing owned opens without changing
  configuration defaults, legacy lifetime caps or compatibility of existing calls.
- Relocate unchanged history value types to
  `src/lib/common/contracts/distributed_operation_history_v2.spl`; preserve
  original journal-module re-exports and all consumer meanings.
- Extend `src/lib/nogc_sync_mut/database/wal_segmented.spl` with checkpoint
  control revisions through existing publication/storage capability.
- Add the two test files named in the verification plan and their authored
  manual only when actual executable scenario content exists.

No changes to `distributed_operation_state_v2`, native runtime exports,
policy/admission baselines, or domain expiry behavior in Slice A. Coordinate
journal/WAL edits with root's frozen Windows foundation before touching source.
Use its existing storage abstraction; no local Windows path fallback.

Stop criteria: this design phase ends after independent review and correction
of concrete findings. Implementation, if separately assigned, ends at reviewed
source and honest NOT_RUN evidence; source-only delivery does not close DAE-05.
Physical GC and tombstone expiry require the specified domain retention contract
and provider support, not a new generic framework or placeholder success.
