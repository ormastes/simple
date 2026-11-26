# Feature expert: Simple Container shared immutable store (increments 1-2)

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
- `std.nogc_sync_mut.storage.immutable_store_v1` — file I/O, so `nogc_sync_mut`.
  Ingest byte-compares on alias hit; collisions get `<algo>_<hex>_c<n>` (n <= 64).
  No-replace publication; `ingest_pinned` ingests and pins atomically w.r.t. GC.
  - Roots: CAS truth is the never-deleted `roots/<name>.g<N>.claim` chain
    (`immutable_store_v1_root_head` reads it); `roots/<name>.sdn` is a cache.
  - Pins are append-only directories: `pins/<id>/owner` and `pins/<id>/refs/<key>`.
  - GC: list-first, then re-check/restore; dry-run default, quarantine, never unlink.
- `std.nogc_sync_mut.storage.storage_view_v1` — host copy-on-write view over the
  store: path policy, quota, volumes, save/load, clone, destroy, lifecycle journal.
- `std.nogc_sync_mut.storage.scv_adapter_v1` — bridges legacy SCV chunks
  (`sha256_<hex>`, identity preserved) into `<repo>/.scv/store`; `pin_reachable`
  writes `scv-gc-<g>-<n>` pins; `scv_adapter_v1_enable` creates the store.
- `std.common.contracts.container.{capability_report_v1, lifecycle_journal_v1}`
  — fail-closed admission (needs `evidence_revision`), pure recovery-action planner.

## SCV opt-in
Nothing creates `.scv/store` by default. Run `scv store-init` in an initialized
repo; afterwards `scv gc` imports and pins reachable chunks (fail closed).

## Testing (Windows host)
Use a Nov-25+ binary, e.g. `C:/dev/keep/seeds/simple-local-20261125.exe test <spec>`.
Specs (test/01_unit/lib/nogc_sync_mut/storage + common): hash_policy 10,
object_record 15, immutable_store 26, scv_adapter 6, storage_view 13 (junction
example is Windows-only via `skip_on_unix`), capability_report 10,
lifecycle_journal 11, system 2, plus `scv_gc_store_e2e_spec.spl` (2).

## Not done
Native provider wiring, SimpleOS pager/PMM, VFS enforcement, live memory-limit
updates; SCV write paths are not hooked (chunks import lazily at gc).
