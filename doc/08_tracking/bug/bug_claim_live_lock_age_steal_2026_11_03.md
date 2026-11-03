# Bug-claim writer locks can be stolen from live owners

Priority: P2. Source repair candidate; focused regression passed, review pending.

The previous `scripts/check/bug-claim.shs` recovered every lock directory older
than two minutes without checking process liveness. A slow live writer retained
its private database snapshot while a second writer could acquire the replacement
lock and publish. The original writer could then publish its older snapshot,
losing the second writer's claim. Exit cleanup also removed the lock directory
by pathname without checking ownership.

Fresh claims physically disappeared during the 2026-11-03 recovery campaign.
This source hazard is confirmed independently; it is **not proof of the exact
cause of those disappearances**. An external database rewrite remains possible.
Incident evidence is retained outside the repository at
`C:/dev/recovery-delete-20261103/claim-loss-investigation/REPORT.md`.

## Repair contract

- A unique owner marker records the writer's shell PID and a `mktemp` token.
- Directory age never authorizes stealing a live owner's lock.
- Recovery checks the shell PID namespace using builtin `kill -0` and `ps -p`;
  the second check preserves an existing process when signalling is denied.
- A reaper may remove only the exact dead owner's marker. Only successful
  removal authorizes `rmdir`, so competing reapers cannot remove a newly created
  replacement directory after losing the marker race.
- Publish checks ownership both before and after private resealing. Cleanup
  removes only its own unique marker before trying to remove an empty directory.
- Ownerless/legacy directories fail closed. Their creator's liveness cannot be
  established safely from age; inspect and recover them manually. Death in the
  narrow interval between `mkdir` and owner-marker creation has this same limit.

Normal reads remain against atomically published real DB snapshots. Writers
still acquire the lock before copying or reading the database for mutation.
No statuses, claim expiry policy, tracker schema or PR admission rules change.

## Focused regression

`python scripts/check/check-bug-claim-lock-owner.py --shell <POSIX-sh>` invokes
the real helper against private fixture databases. Only resealing is replaced
by a bounded barrier; checksum functionality is outside this test's scope.

1. Age an actual live writer's directory by ten minutes without a long sleep;
   start a competing claim, then release the first writer and retain both claims.
2. Recover a marker whose real shell PID has exited, then publish a claim.
3. Replace the lock while a writer is paused; reject stale publish and preserve
   the replacement directory during exit cleanup.

No production claim database is used by these scenarios. Historical claim
holder/status semantics require their existing selftest separately.

## Verification on Windows, 2026-11-03

The live-owner, dead-owner recovery and replacement cleanup/publish scenarios
each passed against the repaired helper. The first collection timed out before
the third fixture reached its reseal barrier on this busy host; its readiness
deadline was increased to90 seconds and only the unfinished scenario was retried.
The live-owner scenario was subsequently strengthened to observe an actual
completed contention attempt rather than relying on a short startup sleep.

The original age-stealing helper fails that same live-owner scenario:
`AssertionError: contender copied DB under a live lock`. On Windows, the fixture
must put the POSIX shell tool directory first on PATH; ambient PowerShell PATH
otherwise resolves `find` to Windows `FIND.EXE`, hiding the original defect.
The repaired helper passes with that corrected POSIX-tool environment.

Shell syntax and whitespace checks passed. Evidence logs and exact review diff
are retained in `C:/dev/recovery-delete-20261103/claim-lock-repair/`.
No normal Simple tests, unrelated green checks or full tracker semantic suites
were rerun. This evidence qualifies the scoped locking protocol, not every
tracker operation or the historical claim-loss incident's exact cause.

## Release reconciliation

Release advanced with PID-only ownership and fail-closed legacy recovery while
this candidate was being published. The conflict resolution preserves its
`BUG_CLAIM_LOCK_RETRIES` setting, parser/verification-wait changes and refusal to
recover legacy `owner.pid` locks automatically. New locks use unique markers;
only those provably dead markers support automatic recovery.

A separate negative control against release commit
`efbd310e067829ba67386a5f246c400b08b744a8` confirms its remaining stale-publish
gap: it still returns `CLAIMED: A` after the fixture replaces the lock while the
writer is resealing. The candidate rejects that publish instead. Thus the
historical age-steal negative control and the current-release stale-publish
negative control establish distinct boundaries.
