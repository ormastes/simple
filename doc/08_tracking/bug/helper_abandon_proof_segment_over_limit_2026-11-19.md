# Helper-abandon proof path segment over the journal limit (2026-11-19)

Status: **FIXED (code)** — verification NOT_RUN (no runnable `simple` binary on this host).

## Defect
`host_helper_abandon_proof_relative_v1` (`src/lib/nogc_sync_mut/orchestration/host_helper_abandon_record_v1.spl`,
landed in #10391/#10458) built

    host-helper-abandon-proof/<sha256(op)>-<abandon_digest>.sdn

Its last segment is 64 + 1 + 64 + 4 = **133 bytes**. The journal's path gate
`distributed_operation_journal_relative_v3` (`src/lib/common/task_runner/distributed_operation_journal_v2.spl`)
refuses any segment over 128 bytes, so `host_helper_abandon_record_publish_v1` returned
`OPERATION_JOURNAL_RECORD_PATH` on its first journal call, every time. The signed helper-abandon (#10466) could
therefore never release a held helper row.

## How it escaped
`test/01_unit/lib/orchestration/host_helper_abandon_v1_spec.spl` pinned the broken string exactly, and its publish
case (which would have failed with `OPERATION_JOURNAL_RECORD_PATH`) was authored but never run — no runnable binary.

## Fix
- The proof path is now two hashed segments, matching the retention-release proof convention (#10481):
  `host-helper-abandon-proof/<sha256(op)>/<abandon_digest>.sdn` (segments 64 and 68 bytes, depth 3 of 4).
- The publish (`host_helper_abandon_record_publish_v1`), the restart re-verify (`host_helper_abandon_recorded_verify_v1`)
  and the evidence arm (`host_helper_abandoned_evidence_v1`) all build the path through this one helper; no other site
  spells it by hand.
- The inline `128` in the journal gate is now `pub val OPERATION_JOURNAL_SEGMENT_LIMIT_V3: i64 = 128` (same value).
- Both journal backends create nested parents: the legacy path loop, and the Linux protected store's
  `parent_v1(relative, create: true)` (the retention-release proof already relies on it).
- The Windows journal store keeps its own copy of the bound (`runtime_windows_journal_store_v1.h`: at most 4 segments
  of at most 128 characters); the new path passes it too.

## Siblings checked (not affected)
| path builder | longest segment (worst case) |
|---|---|
| service-handoff abandon proof `service-handoff/abandon-proof-<seq>-<digest>.sdn` | 102 bytes at i64::MAX |
| retention-release proof `host-retention-release-proof/<sha(op)>/<digest>.sdn` | 68 bytes |
| remote-run `host-remote-build/<sha(fence,op)>.input-<idx>.sdn` (and open/bundle/reap/reset) | 94 bytes at i64::MAX |

## Migration
None. Every publish at the old path was refused by the gate before any byte was written, so no proof or marker exists
at the old shape.

## Regression spec
`test/01_unit/lib/orchestration/journal_proof_path_segments_v1_spec.spl` (NOT_RUN) — every helper-abandon,
service-handoff, retention-release and remote-run path passes `distributed_operation_journal_relative_v3` and every
segment is `<= OPERATION_JOURNAL_SEGMENT_LIMIT_V3`, with worst-case inputs; the old shape is asserted refused.
