# Feature expert: Simple Container shared immutable store (increment 1)

**Docs:** architecture `doc/04_architecture/platform/container/simple_container_improvement.md`,
design `doc/05_design/platform/container/simple_container_improvement.md`,
plan `doc/03_plan/platform/container/simple_container_improvement.md`.

## Modules
- `std.common.hash.hash_policy_v1` — `hash_policy_v1_digest(policy, bytes)`:
  `xxh3-128` (default), `gxhash-128` (pinned `gxhash-4.0.0-scalar`, in-tree
  pure-Simple port), `blake3-256`, legacy `sha256`. Unknown policy ->
  `status: "unsupported"`; never falls back to another algorithm.
- `std.common.storage.object_record_v1` — SDN `ObjectRecordV1` + digest
  aliases; strict decode, invalid -> `format_version: 0`.
- `std.nogc_sync_mut.storage.immutable_store_v1` — does file I/O, so it lives
  in `nogc_sync_mut`, not `common`. Ingest byte-compares on alias hit;
  collisions get `<algo>_<hex>_c<n>` (n <= 64). No-replace publication, CAS
  roots by generation, pins, GC dry-run default and quarantine (never unlink).
- `std.common.contracts.container.{capability_report_v1, lifecycle_journal_v1}`
  — fail-closed admission (needs `evidence_revision`), pure recovery-action
  planner; executors live in platform leaves.

## Testing (Windows host)
Old seeds (`C:/dev/seeds/simple-release.exe`) fail on the current test runner
(`unknown decorator @representation_boundary`). Use a Nov-25+ binary, e.g.
`C:/dev/keep/seeds/simple-local-20261125.exe test <spec>`. 56 examples across
6 specs (5 unit + `test/03_system/app/container/feature/simple_container_store_v1_spec.spl`).

## Not done (later architecture phases)
Native provider wiring, SimpleOS pager/PMM, VFS enforcement, live memory-limit
updates, SCV internal rewiring onto this store.
