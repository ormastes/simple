# src/compiler_rust/lib/ stdlib-snapshot provenance unknown — 2026-08-28

Found while adjudicating the `check-no-direct-rt.shs` `--roots` widening
(examples/tools/scripts/test scan roots).

`src/compiler_rust/lib/` holds 724 `.spl` files (`std/src/`, `std/examples/`,
`std/shaders/`, `std/report/`, plus a top-level `src/`, `tests/`) — a bundled
stdlib-shaped snapshot inside the `simple-term-io`/`compiler_rust` crate.

## What was checked

- Layout does NOT match `src/lib/`'s layered structure
  (`common/`, `nogc_sync_mut/`, `gc_async_mut/`, ...); the file
  `src/compiler_rust/lib/std/src/__init__.spl` has no counterpart at
  `src/lib/__init__.spl`.
- `grep -rl "compiler_rust/lib" scripts/` found no sync/regen script wiring
  this tree from `src/lib/`.
- `git -C src/compiler_rust log` on one sampled file shows repo history but
  nothing that identifies it as auto-generated vs. hand-maintained.

## Open question (unresolved by this pass)

Whether `src/compiler_rust/lib/` is:
1. a generated/staged copy synced from `src/lib/` by a mechanism not found
   in this pass, or
2. a stale, independently-maintained fork that has drifted from `src/lib/`.

## Interim disposition

Excluded from the `check-no-direct-rt.shs` ratchet
(`scripts/check/no_direct_rt_allowlist.txt`, entry
`src/compiler_rust/lib/`) as derived/bundled crate content — same class as
the `vendor/**` exclusions in `CLAUDE.md`'s Owned-Code Scope — pending
resolution of the open question above. This is NOT a claim that the tree is
safe to ignore for other purposes (doc coverage, lint, drift audits); it is
scoped to this one ratchet only.

## Next action

Whoever owns `src/compiler_rust` build tooling should confirm whether a
sync step exists (and wire it into this record) or whether this tree needs
a dedicated drift-detection gate against `src/lib/`.
