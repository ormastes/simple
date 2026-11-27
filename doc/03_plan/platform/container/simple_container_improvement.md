# Agent task plan — Simple Container Improvement, increment 1

- Store sweeper and cross-owner follow-ups (Fable review, 2026-11-27):
  - An unrestorable foreign pin now stays in a tomb marked `keep`, and the call returns `pin-owner-changed-unrestored`. Nothing yet surfaces or reclaims these tombs.
  - A pin restored as `<id>.r<n>` is not discoverable by its owner, so its refs are retained indefinitely.
  - There is still no directory sync: after a crash, a record can persist while its object rename does not.
  - The collect-path sweep spec runs on an uninitialized root, so only the direct `sweep_staging` calls are proven.
Remaining work after increment 3: `doc/03_plan/platform/container/simple_container_remaining_work.md`.

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

Lane B open items (Fable review 2026-11-26, not fixed here): create has a crash window between view-dir creation and the journal/meta writes; a stale view handle can still reach volume dirs after destroy; `rt_dir_walk` swallows read_dir errors so the upper scan can fail open; `rt_dir_remove_all` may follow ancestor junctions during destroy.

## Review follow-ups (Fable review 2026-11-26)

Fixed in increment 1: root CAS made atomic via no-replace `roots/<name>.g<N>.claim`
(the claim chain is the truth and is never deleted; the pointer is a cache)
with crash roll-forward; GC fails closed when `roots/` or `pins/` is missing or
unlistable; alias-to-missing-object republish requires matching digest hex; GC
quarantine move is no-replace; launch qualification rejects an unavailable
client authority.

Open (P2, next increment):
- Storage view: a junction swapped in between the parent walk and the open still redirects (closing it needs handle-relative opens; out of path-policy scope).
  - Upper shadowing (fixed 2026-11-27): an upper FILE at `a` hides base `a/b` (read returns `missing`/`path-shadowed`, no fall-through); an upper DIR `a/` falls through to base paths it does not override. Specced.
  - Save entry cap (fixed 2026-11-27): save takes its cap via `_sv_save_inner` (public save passes `_SV_MAX_FILES`); a spec drives save with a small cap and expects `manifest-too-many-entries` with no new objects.
  - File/dir conflicts (fixed 2026-11-27): write rejects `path-conflict` when base has an entry under `P/` or a file at an ancestor of P; save fails closed with `manifest-path-conflict`; both fold case.
- DONE (work/scv-adapter-legacy-pin-20261127): SCV adapter keeps the pin for a digest-mismatched legacy blob whose key the store still opens `ok` (verified via `immutable_store_v1_open`, never the blob); a mismatched blob with no stored copy stays skipped. Specs in `scv_adapter_v1_spec.spl` (9/9).
- Atomic pin creation (done 2026-11-27): a new pin is built in `staging/pincreate-*/pin` (owner + refs, synced) and renamed into `pins/<id>`, so GC and release never see a half-created ownerless pin. An existing `pins/<id>` keeps the in-place merge semantics (same owner merges refs, other owner = `pin-owner-mismatch`). POSIX rename(2) replaces an EMPTY destination dir, so the destination is checked first; staged pins are never empty (owner file), so racing creators cannot replace each other. Residual: an empty `pins/<id>` appearing between the check and the rename. The sweeper also removes stale `pincreate-*`. Release of a legacy ownerless dir stays allowed.
- Atomic pin creation residual (done 2026-11-27): `_isv1_pin_add_in_place` no longer creates `pin_dir`; refs/ is made with exclusive `dir_create_new` (parent must exist), and a vanished pin returns `pin-vanished`, upon which `_isv1_pin_add` retries the staged create (`_isv1_pin_add_staged`, max 3 attempts, then `pin-contended`). The losing-rename path is specced by driving `_isv1_pin_add_staged` against an existing pin (merge, `pin-owner-mismatch`, no staging residue).
- RESOLVED (2026-11-27) GC quarantine restore follow-ups: `_isv1_restore_reachable` probes quarantine first and returns on no copy (a plain miss is one stat per day dir; roots/pins are read only when a verified copy exists). `rt_file_publish_noreplace` returns -1 for a missing source on every lane (interpreter, C, Windows), so `_isv1_restore_moved` treats -1 with source gone and target present as settled (no spurious `restore-failed`). A publish in-branch retry that returns 0 re-reads the reappeared winner instead of `publish-winner-unreadable`. Specs: store 42 -> 44.
- View create crash follow-ups (Fable review, 2026-11-27):
  - Atomic staging residue (fixed 2026-11-27): `_sv_destroy_half_created` now accepts a real `.simple-atomic-bytes-*/` dir holding at most its `payload` file; anything else in it is still refused. Specced.
  - Recovery now reaches a same-id create caught between its claim and its journal write. This is acceptable only because destroying an id you do not own is a caller error.
- release_pin across owners (fixed 2026-11-27): after the rename-aside `_isv1_release_pin_finish` re-reads `<tomb>/pin/owner`; a different owner's pin is renamed back (to `pins/<id>`, or `pins/<id>.r<n>` when the id was re-created, never clobbering) and `pin-owner-changed` is returned. Residual: the owner-b pin is briefly absent from `pins/` between the two renames (GC may miss its refs for that window; a GC concurrent with a cross-owner release); if id is so long that no `.r<n>` name fits and `pins/<id>` is taken, the pin stays in the tombstone and the staging sweeper will eventually delete it.
- Staging sweeper (done 2026-11-27): non-dry-run `collect` calls `immutable_store_v1_sweep_staging`, removing `staging/{pinrel,ingest,publish}-*` dirs whose directory mtime is >= 3600 s old (conservative; no pid/nonce marker exists, so liveness is unprovable; a single payload write stalling an hour would be lost). Unknown mtime keeps the entry. `init` does not sweep.
- RESOLVED (2026-11-27): `open` keeps `ok` meaning "present under objects/". On a miss for a currently reachable key (`_isv1_reachable`, GC's own restore condition) it restores the digest-verified quarantine copy no-replace and reads from `objects/`; an unreachable collected key stays `missing`. Publish retries the no-replace publish from the still-existing stage (bounded, pinned or not) before reporting `publish-winner-unreadable`. Quarantine scan: 4096 day dirs, contiguous `_n` slots.
- Staged publishes now `file_sync` the staged file before the no-replace rename (both `_isv1_publish` and `_isv1_publish_text_noreplace`; failure rejects). Open: no directory-sync primitive exists in SOSIX, so the rename itself is not made durable.
- Root claims accumulate (one file per generation, never deleted); compaction needs a design that cannot reopen a claimed slot.
- DONE (2026-11-27): `substring` is byte-indexed in the interpreter and native (`rt_slice_text_bytes`); an end past the length clamps (no panic), and a bound inside a multi-byte char yields U+FFFD (lossy, not an error), so `substring(n, byte_len())` is safe by itself but `_isv1_unquote`'s one-byte slices silently mangled non-ASCII (a root doc with `name: "ma\u{e9}n"` decoded as ok). `_isv1_doc_decode` now rejects any byte >= 128 up front (`non-ascii`); spec: "rejects a root doc carrying non-ASCII bytes" in `immutable_store_v1_spec.spl` (30 -> 31). Other increment-1 decoders have no `substring(.., byte_len())` on disk/peer input.
- Pointer-cache write failures are ignored; an unrefreshable pointer bricks a root after 4096 generations (`root-claim-chain-too-long`).
- Drop the `.value` condition reads on the new bool units once the seed bool-unit bug is fixed.
- Specs: no gxhash known-answer vector through the policy; lost-race publish path not exercised.
- SCV adapter generation race: concurrent `scv gc` runs can release each other's fresh `scv-gc-<g>-<n>` pins; the next import/pin run heals it (re-import is idempotent).

Pin release (2026-11-27): `release_pin` renames the pin dir to a fresh path under `staging/pinrel-*` (via SOSIX `rename_path`; ownership decided by the rename, GC never scans staging) then deletes it; `ingest_pinned` re-checks its ref after the write and returns `pin-released`. Seed note: `rt_file_publish_noreplace` on non-Linux seeds is hard-link based and cannot move directories, so the plain rename to a unique path is used.
Increment 3 Lane C status (2026-11-26): storage_view junction spec is Windows-only (`only_on_windows`); opt-in `scv store-init` (`scv_adapter_v1_enable`) added; `scv_gc_store_e2e_spec.spl` covers gc with and without `.scv/store`. Verification limits on the Windows host (2026-11-26): single-file `simple check` cannot resolve any std module surface (`missing module surface for std.…`) — an untouched baseline `src/lib/scv/store.spl` fails identically, so `check` gives no signal for these modules; `check-io-runtime-facade-imports.shs` did not finish in 40 min (rc=124). Evidence is interpreter specs + the two `--changed` gates + CI required gates.
Status 2026-11-26 (Increment 3 Lane E): Windows job-object hard memory cap measured Enforced on this host (under 208805888 <= cap 276824064; over denied, peak 310333440, exit 0xC0000409; uncapped baseline OK); Windows capability report affirms memory_hard_limit/job-commit only from that verdict. See design doc "Increment 3 Lane E".

Status 2026-11-27 (storage view hardening, Lane B open items): fixed in `storage_view_v1.spl`.
- Destroy ancestor junctions: `rt_dir_remove_all` canonicalizes its argument first, so a junction on the view dir (an ancestor of `upper`) redirected the delete to the junction target even though `upper` itself looked like a real dir. Destroy now requires `view_root` and `view_root/<id>` to be real non-reparse dirs (`view-dir-not-real-dir`) in addition to the existing `upper` check. Junctions found inside the tree are not followed by the runtime's `std::fs::remove_dir_all` (modern Rust unlinks reparse points). Residual: ancestors above the caller-supplied `view_root` are the caller's trust anchor and are not checked. Create now also refuses a non-real `view_root` (`view-root-not-real-dir`). Residual (P2): a swap between the real-dir checks and the canonicalize inside `rt_dir_remove_all` still redirects the delete. This is the same class as the walk/open swap, and closing it needs handle-relative removal.
- `rt_dir_walk` fail-open: the upper scan now walks with `dir_list_optional` (nil = refuse, `upper-unreadable`) and rejects a non-real subdirectory (`upper-entry-not-real-dir`). Residual: `rt_dir_list` still drops per-entry errors and non-UTF-8 names inside a readable directory.
- Stale handle: write/read/add_volume/save/clone re-check that the view root and view dir are real dirs and the journal is present and not destroyed (`view-destroyed`) before touching volume dirs.
- Create crash window (fixed 2026-11-27): a create that crashed after claiming the view dir leaves a dir with a missing or unparseable journal. `storage_view_v1_destroy` now recovers it (the id can then be re-created): it removes the dir only when the journal is missing/unreadable/invalid AND the dir holds just journal.sdn, view.sdn (plain files) and an empty real upper/; any other entry or a non-empty upper is refused untouched, and a valid-journal view still goes through the normal journaled destroy. Specs: 3 added to `storage_view_v1_spec.spl` (18/18), plus 4 recovery specs (22/22).
