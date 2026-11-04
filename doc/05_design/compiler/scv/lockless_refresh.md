# Lockless SCV refresh (inventory, snapshot, workaround index)

Status: implemented 2026-11-04 (replaces PR #6541's 900 s lock wait).
Directive: "the compiler must be LOCKLESS." Parallel stage3 compiles on one
project root failed with `SCV-E-ADMISSION: compile-event-refresh-lock-unavailable`
and `workaround writer lock unavailable`; both locks are gone.

## Invariants

1. **Readers never lock.** Every published object is immutable and
   content-addressed: `source-inventory/generations/<sha256>.inventory`,
   `compile-events/untracked/<sha256>.paths`, `snapshots/scv-revision-v1-<hash>/`,
   `objects/chunks/<sha256>.blob`, `.simple/workarounds.d/<clock>-<pid>-<hash>.sdn`.
   A reader that resolves a name sees complete bytes or nothing.
2. **Writers never lock.** A writer builds into a private stage named by
   `pid + clock` (`<final>.tmp.<pid>.<micros>`, `.tmp.<pid>.<mkdtemp>/`), then
   publishes with `file_publish_noreplace_raw` (Windows / `renameat2(RENAME_NOREPLACE)`
   / POSIX `link`). If the final name already exists with the same bytes the
   loser discards its copy: an identical-content race is benign.
   Nothing is ever written in place; a partial stage never carries a final name.
3. **Mutable pointers are tiny and swapped atomically.**
   `source-inventory/CURRENT` (inventory digest + event cursor) is replaced by
   one atomic rename (`file_atomic_write`). Compare-and-swap is done by
   re-reading CURRENT against the base the writer observed, immediately before
   the swap: moved-with-our-bytes -> `ok`; moved otherwise ->
   `publish-cursor-superseded`, and the refresh owner re-observes warm from the
   winner's pointer (bounded to 4 attempts, `COMPILER_INVENTORY_REFRESH_ATTEMPTS_V1`).
   The rename itself is the only window a same-base publisher can win; its
   pointer also names a complete generation, so the next refresh simply
   re-derives from whichever won. A slightly old pointer is always safe.
   The former `publish-generation-digest-divergence` wedge is gone: same
   generation + different content is a race, not corruption.
4. **Workaround index = fragments merged at read.** Each refresh publishes one
   immutable fragment (`base`: whole index, or delta: exactly the paths it
   re-read + their links). `load_workarounds_at` folds fragments in name order
   (`replace_workaround_paths` per delta), so concurrent writers on different
   paths never lose each other's rows. A base fragment is written on full
   scan, on first publication over the legacy single file, and as compaction
   once 32 fragments exist. No-change refreshes publish nothing.
5. **GC is lock-free and age-based.** Only unreferenced objects older than a
   floor are deleted, and a delete that loses to a concurrent sweep is not an
   error: generations/membership 24 h (`compiler_inventory_gc_v1`; shard
   children re-read their admitted generation by digest hours into a build),
   snapshots `SIMPLE_SCV_SNAPSHOT_MIN_AGE_S` (600 s, LRU, never `keep`),
   fragments superseded by a later base + 600 s, dead-pid stages via
   `compile_source_inventory_recover_v1`.

## What was removed

- `src/app/compiler_entrypoint/inventory_refresh_lease.spl` (the lease,
  `refresh.lock`, `SIMPLE_SCV_REFRESH_LOCK_WAIT_S`) - deleted, no wrapper (MIG-01).
- `publication.lock` in `compile_source_inventory.spl` (publish, revalidate, recover).
- `.simple/workarounds.sdn.lock` and the `workaround_host_lock/unlock` seam.
- `.build-retention-v1.lock` in the unmanaged snapshot collectors
  (`compile_snapshot_retention_v1.spl`). The managed build-retention store
  (`build_retention_store_v1.spl`, pins/leases) keeps its own authority and is
  outside the compile refresh path.
- Eager deletion of the previous membership record after publish (a concurrent
  observer may still read it) and of a newly written record after a failed
  apply - both replaced by GC.
- `lock_released` on `CompilerInventoryTraceV1` / `ScvCompileCostV1`.

## Prevention

`scripts/check/check-no-refresh-file-lock.shs` (fail-closed, `--selftest`,
runner `test/01_unit/scripts/no_refresh_file_lock_test.shs`) flags any
`file_lock`/`file_unlock`/lock-alias site in `src/app/compiler_entrypoint/`,
`src/lib/scv/compile_*.spl`, `src/app/bug/workaround_store.spl` and the
workaround host seam.

## Evidence

- `test/01_unit/lib/scv/compile_source_inventory_lockless_publish_spec.spl`:
  no lock file; identical-content race -> ok; different-content race ->
  superseded; blob publish idempotent; writer killed between stage and
  publish leaves readers on the old complete generation and is reclaimed; GC
  age floor.
- `test/01_unit/app/bug/workaround_fragment_spec.spl`: codec, merge, no lost
  update, base replacement, completeness fold.
- `test/01_unit/app/compiler_entrypoint/lockless_refresh_stress_test.shs`:
  N concurrent cold + warm refreshes on ONE checkout + ONE cache root
  (all succeed, converge on one digest/generation, no lock file, no lock
  diagnostic), readers during 40 publishes never see an incomplete
  generation, 8 concurrent workaround writers merge to 8 links.
- Stage3: c01..c20 in parallel on one shared s3sanity root (see the PR).
