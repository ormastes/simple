# Agent task plan — Simple Container Improvement, increment 1

**Date:** 2026-11-25
**Design:** `doc/05_design/platform/container/simple_container_improvement.md`
**Architecture:** `doc/04_architecture/platform/container/simple_container_improvement.md`
**Lane branch:** `work/container-improvement-20261125` (worktree `C:/dev/lanes/container-impl`, base `release/1.0.0` @ `64dfa6d980f`)
**Merge owner:** Kimi session (this lane); lands via PR to `release/1.0.0`.
**Final reviewer:** highest-capability review of the merged lane diff before PR merge (zero P0/P1).

## Lanes

| Lane | Files owned (exclusive) | Depends on | Status |
|---|---|---|---|
| A — hash policy | `src/lib/common/hash/hash_policy_v1.spl` | design doc signatures | done |
| B — immutable store | `src/lib/common/storage/object_record_v1.spl`, `src/lib/nogc_sync_mut/storage/immutable_store_v1.spl` | A signatures (from design doc, not A's file) | done |
| C — container contracts | `src/lib/common/contracts/container/capability_report_v1.spl`, `src/lib/common/contracts/container/lifecycle_journal_v1.spl` | none | done |
| D — specs | `test/01_unit/lib/common/hash/hash_policy_v1_spec.spl`, `test/01_unit/lib/common/storage/object_record_v1_spec.spl`, `test/01_unit/lib/nogc_sync_mut/storage/immutable_store_v1_spec.spl`, `test/01_unit/lib/common/contracts/container/capability_report_v1_spec.spl`, `test/01_unit/lib/common/contracts/container/lifecycle_journal_v1_spec.spl`, `test/03_system/app/container/feature/simple_container_store_v1_spec.spl`, generated `doc/06_spec/03_system/app/container/feature/simple_container_store_v1_spec.md` | A+B+C merged into lane branch | done |

## Shared interface contract

All cross-lane names, struct fields, constants, and failure sentinels are fixed by
`doc/05_design/platform/container/simple_container_improvement.md` §"Interfaces and storage". Sidecar
lanes must not rename or reshape them; deviations are merge blockers.

Fail-fast rule: if a lane cannot complete a function, it leaves an explicit
`fail("unimplemented: <name>")` body — never a silent no-op or `expect(true)`-style stub.

## Sidecar policy

Lower-model sidecars: `N/A` (single-model parallel coder lanes this increment).
Final merge review by the coordinating session at highest capability before PR.

## Verify gate before PR

- `bin/release/<triple>/simple check src/lib/common` (and the changed subtrees)
- Unit specs green: `bin/simple test test/01_unit/lib/common/storage/ test/01_unit/lib/common/hash/hash_policy_v1_spec.spl test/01_unit/lib/common/contracts/container/`
- System spec green + `bin/simple spipe-docgen` mirror generated, `0 stubs`
- `find doc/06_spec -name '*_spec.spl' | wc -l` → `0`
- No edits outside owned files; no changes to existing SCV behavior (legacy identity preserved)

## Status 2026-11-26

Increment 1 implemented and verified: 6 specs / 60 examples green on the Windows host. `immutable_store_v1` moved to `src/lib/nogc_sync_mut/storage/` (it does file I/O; `common/` is pure). Docs moved under `doc/<phase>/platform/container/`. Spec mirror generated. Lands via PR to `release/1.0.0`.

## Status 2026-11-26 — Increment 2 Lane 0

Lane 0 (store API/format hardening, `work/container-inc2-hardening-20261126`) implemented items 1-7: counted root/pin docs, canonical integers, `immutable_store_v1_ingest_pinned`, pin owner check (`release_pin` now takes `owner`), aligned 4 MiB pin bound with `_ISV1_MAX_REFS` 16384, GC stem validation, and domain units in `object_record_v1`/`hash_policy_v1`. Existing stores written before the `count` field are rejected by decode (no non-spec consumers yet). Review fixes: pins are now append-only directories (`pins/<id>/owner`, `pins/<id>/refs/<key>`, no-replace publication, no lost updates or owner races); GC lists candidates before reading roots/pins and re-reads them after moving, restoring any key that became reachable (a reader may transiently see `missing`); root docs require a terminating newline and bare (unquoted) integers; pinned-ingest reuse paths republish if GC quarantined the object.

## Status 2026-11-26 — Increment 2 Lane A

Lane A (SCV adapter, `work/container-inc2-scv-adapter-20261126`): `scv_adapter_v1.spl` imports legacy `sha256_<hex>` chunks with identity preserved, projects them back, and `scv gc` pins reachable chunks (generation-based `scv-gc-<g>-<n>` pins, owner `scv`) when `<repo>/.scv/store` exists; repos without it are unchanged. Specs: `test/01_unit/lib/nogc_sync_mut/storage/scv_adapter_v1_spec.spl`.

## Status 2026-11-26 — Increment 2 Lane B

Lane B (`work/container-inc2-storage-view-20261126`) implemented `src/lib/nogc_sync_mut/storage/storage_view_v1.spl` (host copy-on-write view: create/open/add_volume/write/read/save/load/clone/destroy) with `storage_view_v1_spec.spl` (9 examples). Path-policy confinement only, not kernel confinement; no whiteouts; `load` uses a fixed 64 MiB default quota; clone does not carry volumes.

## Review follow-ups (Fable review 2026-11-26)

Fixed in increment 1: root CAS made atomic via no-replace `roots/<name>.g<N>.claim`
(the claim chain is the truth and is never deleted; the pointer is a cache)
with crash roll-forward; GC fails closed when `roots/` or `pins/` is missing or
unlistable; alias-to-missing-object republish requires matching digest hex; GC
quarantine move is no-replace; launch qualification rejects an unavailable
client authority.

Open (P2, next increment):
- SCV adapter: a digest-mismatched legacy blob is skipped, which drops the store pin for an already-imported good copy (quarantine-recoverable). Keep the old pin for keys already in the store.- Ownerless pin release can race a concurrent creator between `dir_create_all` and the owner publish (the creator fails loudly with `pin-write-failed`).
- release_pin vs a same-owner concurrent ingest_pinned: ingest returns ok for a ref the release then deletes. Lanes must not release a pin they still ingest into.- release_pin is not atomic across owners (`dir_remove_all` order); rename the pin dir aside before deleting.- A GC move-then-restore can make `open` briefly return `missing` on a reused object; a GC that moves the winner mid-publish yields a spurious `publish-winner-unreadable`.- `_ISV1_MAX_REFS` is per call; total refs per pin are unbounded. Base-key refs from lost races over-retain.
- Staged publishes do not fsync.
- Root claims accumulate (one file per generation, never deleted); compaction needs a design that cannot reopen a claimed slot.
- `substring(..., byte_len())` on non-ASCII hostile lines in doc/record decode: confirm `substring` clamps (fail-closed) or reject non-ASCII first.
- Pointer-cache write failures are ignored; an unrefreshable pointer bricks a root after 4096 generations (`root-claim-chain-too-long`).
- Drop the `.value` condition reads on the new bool units once the seed bool-unit bug is fixed.
- Specs: no gxhash known-answer vector through the policy; lost-race publish path not exercised.
- SCV adapter generation race: concurrent `scv gc` runs can release each other's fresh `scv-gc-<g>-<n>` pins; the next import/pin run heals it (re-import is idempotent).
