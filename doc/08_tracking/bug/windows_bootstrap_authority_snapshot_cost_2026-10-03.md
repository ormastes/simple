# Windows bootstrap spends substantial time on authority snapshots

Status: measured phase overhead; unresolved optimization opportunity.
Scope: item-3 bounded bootstrap recovery at source pin `1d9824fe2d1`.
No before/after baseline exists, so this report does not establish a regression.

Recovery cycle 1 recorded 562 seconds for its fingerprint phase. Cycle 3
recorded 388 seconds for completed bootstrap preflight and then remained in
source snapshot hashing before compiler launch. At 06:07:49 UTC the owned
Perl hashing processes used Digest::SHA and Time::HiRes stat/lstat. These are
phase measurements, not isolated timings of a particular hash implementation.
Evidence is retained under the specification worktree's Git metadata:
`item3-bootstrap/recovery-20261003/`.

Read-only review of the pinned scripts explains repeated integrity checks:

Sources: `scripts/check/lib/bootstrap-stage3/command-snapshot.shs`,
`scripts/check/check-bootstrap-preflight.shs`,
`scripts/bootstrap/resume-stage3-from-admitted.sh`, and
`scripts/check/lib/bootstrap-stage3/authority.shs`. Line references below use
the pinned revision.

- `command-snapshot.shs:728` takes two independent source snapshots and compares
  both hashes and bytes. The single snapshot implementation at line 497 walks
  authority files, hashes them, checks read identities and performs a final
  identity sweep. Its roots at line 719 include `src` and selected bootstrap,
  example and test paths, with explicit exclusions.
- Preflight binding capture calls that snapshot operation. Receipt creation
  captures twice; receipt verification captures again. The resume path also
  obtains fresh source snapshots before compilation. These are integrity
  intervals, not evidence that the compiler has hung.
- Producer fingerprinting is a separate Rust/runtime/Cargo/helper domain.
  Its path-list hasher already batches work and can shard it. Do not attribute
  the entire observed phase cost to per-file process launches.

Possible bounded experiment: enumerate a canonical authority list in the
parent, use two workers for file reads/hashes within one snapshot operation,
then retain parent-authoritative ordering and final identity checks. Preserve
both independent snapshots, all link/no-follow and stat/fstat checks, and every
receipt boundary. This proposal is unimplemented and may be slower on a
contention-limited filesystem; measure it before adopting it.

Acceptance requires byte-identical manifests on stable fixtures; rejection of
mutation during reads, identity/link changes and worker failures; bounded
memory/process counts; and separately timed unchanged and changed trees on
the same host. Never substitute HEAD, mtimes or manually rewritten stamps for
content identity. Existing caches and the final recovery attempt remain intact.
