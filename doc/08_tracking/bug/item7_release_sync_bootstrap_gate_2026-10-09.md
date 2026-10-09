# Item 7 release synchronization and bootstrap gate

Status: locally rebased; bootstrap admission refused; not pushed.

The preserved `work/item7-completion-20261003` branch at
`117a32274faa96b183d603992e08b40e54f9b294` was recovered into the isolated
`C:/dev/simple-item7-sync-20261009` worktree on `work/item7-sync-20261009`.
Its commits were rebased onto fetched `release/1.0` at
`c81c8080039215961747b86d481278080d75b375`. Rebased implementation head:
`d876cb6795f`. The old branch and unrelated dirty main worktree were preserved.

Conflicting additive imports were combined. Already-landed watchdog changes
were not reapplied over newer release/FreeBSD behavior. Read-only review of
seven overlapping compiler files confirmed preservation of retained-owner HIR
checks, K1 callbacks, canonical object paths, BFD probing, diagnostic retention,
newunit resets, codec reader construction, lock imports, and semantic policy.
The rebased tree has 142579 tracked files versus release's 142547: 32 additions,
61 modifications, zero deletions. The full release-to-head whitespace check passed.
These are source/integration checks, not runtime verification.

## Actual bootstrap check

Executed from the rebased worktree with an isolated storage root and a 30-second
bound:

```sh
SIMPLE_WORKTREE_STORAGE_ROOT=/c/dev/simple-item7-sync-20261009/build/item7-bootstrap-check \
timeout --kill-after=3s 30s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --validate-bootstrap-receipt
```

Exit **64**: `bootstrap-policy-error: reason-receipt-required`.
Logs: `build/item7-sync-evidence-20261009/bootstrap-admission.log` and
`bootstrap-admission.exit`. No build stage started. A preliminary scripts-only
archive check lacked the kernel policy manifest and was not considered evidence
of a bootstrap regression; the complete-worktree refusal above is authoritative.

The newer Windows producer under `build/rc1-newp2-hello40-preparation/producer`
remains diagnostic-only: its qualification failed outer process-owner cleanup.
Other sessions' successor and item3 builds were left untouched. No admitted full
CLI was discovered. Before pushing as stable, obtain a canonical planner receipt
bound to an admitted parent, runtime snapshot, planner and current source, then
run bootstrap and the pending compiler acceptance checks. Do not fabricate
authority or substitute diagnostic binaries. Full item 7 coding, runtime
verification, and the mutable-link-input receipt repair remain incomplete.
