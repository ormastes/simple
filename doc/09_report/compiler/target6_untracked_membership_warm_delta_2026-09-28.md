# Target 6 warm untracked-membership delta (2026-09-28)

Warm Git inventory refresh previously compared an untracked-membership hash
and required a full cold initialization whenever it changed. Removing one
untracked `.spl` source therefore made an otherwise valid warm compile fail.

The atomic `source-inventory/CURRENT` record now uses cursor V3. It binds the
digest of an immutable, bounded untracked-path record under
`build/scv/compile-events/untracked/`. The record is written and read back
before the pointer is published. A warm refresh with unchanged membership
keeps the existing digest. On membership change it reads the old record,
reconciles removed paths against Git's cached paths, and emits delete events
only for paths that are neither tracked nor currently untracked. New
untracked paths already enter through the existing create events. Unrequested
`src`/`test` scopes retain their previous membership. A missing or corrupt
record fails closed with an explicit cold-recovery reason. V1/V2 cursors
remain readable, but must be cold-initialized once to acquire V3 membership
authority.

Focused bootstrap-interpreter SPipe evidence on this worktree:

- `compiler_inventory_cold_recovery_spec.spl`: 1/1 passed, including warm
  untracked deletion, creation, and staging into Git's index.
- `compile_source_inventory_spec.spl`: 20/20 passed, including V3 cursor
  publication and the 768-byte CURRENT bound.
- `compiler_inventory_unicode_untracked_spec.spl`: 1/1 passed with literal
  UTF-8 path identities. Its old V1 cursor expectation and integer cleanup
  assertion were updated to the current API; two earlier diagnostic runs
  failed on those stale assertions, then the corrected run passed.
- `compiler_inventory_untracked_membership_corrupt_spec.spl`: 1/1 passed.
  Corrupting the content-addressed path record and then changing membership
  was rejected without replacing the atomic CURRENT pointer.
- `compiler_inventory_untracked_membership_gc_spec.spl`: 1/1 passed.
  Successful warm create/delete transitions retire the prior path record
  after the new pointer is admitted under the refresh lock.

This does not meet the full Target 6 gate. The path list and Git untracked
enumeration still run on every warm request; the rare membership-change path
adds one cached-path enumeration. No current-source native binary, 30-sample
time/RSS comparison, concurrent-writer fault matrix, or complete graph-index
entrypoint cutover has passed. The old Stage2/full-CLI limitation remains.
An interrupted or rejected publication can still leave an unreferenced
content-addressed path record; recovery/GC for those orphans remains open.
