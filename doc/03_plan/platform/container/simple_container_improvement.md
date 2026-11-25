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

## Review follow-ups (Fable review 2026-11-26)

Fixed in increment 1: root CAS made atomic via no-replace `roots/<name>.g<N>.claim`
(the claim chain is the truth and is never deleted; the pointer is a cache)
with crash roll-forward; GC fails closed when `roots/` or `pins/` is missing or
unlistable; alias-to-missing-object republish requires matching digest hex; GC
quarantine move is no-replace; launch qualification rejects an unavailable
client authority.

Open (P2, next increment):
- Pin refs bound (65,536) exceeds the 1 MiB pin read bound; align the limits.
- Root/pin doc decode has no count/terminator, so line-boundary truncation decodes as valid; staged publishes do not fsync.
- Pin overwrite ignores owner and is read-then-write; ingest takes no pin, so a `reused: true` key can be collected before it is rooted.
- Non-canonical integers (`_c01`, `generation: 007`) are accepted.
- Root claims accumulate (one file per generation, never deleted); compaction needs a design that cannot reopen a claimed slot.
- Specs: no gxhash known-answer vector through the policy; lost-race publish path not exercised.
