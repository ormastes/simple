# Six part-files under `_<Name>/` split directories are never imported, so nothing compiles them

- **id:** orphaned_part_files_never_imported_2026-09-18
- **status:** OPEN (one deleted; six remain, now ratcheted)
- **severity:** P2 — dead source is cheap on its own, but it silently absorbs fixes,
  diverges from the live copy, and reads as authoritative to anyone grepping
- **found:** 2026-09-18, while closing
  `duplicate_impl_method_definitions_silent_first_wins_2026-08-08.md`

## What was measured

This repo splits an over-long module into a `_<Name>/` directory whose files the
parent module re-exports. Of the **238** such part-files in `src/`, **six** have a
module path that no `use` anywhere in the repository names. Nothing imports them,
so nothing ever compiles them.

| part-file | lines | note |
|---|---|---|
| `src/app/io/_CliCompile/native_build.spl` | 851 | superseded original — see below |
| `src/os/services/evidence/_verifier_owner/verifier_transactions.spl` | 356 | not yet analysed |
| `src/os/port/_initramfs_pack/archive.spl` | — | its only sibling `support.spl` is imported by it and nothing else |
| `src/lib/gc_sync_mut/tls/_TlsUtilities/hex_encoding.spl` | — | a re-export shim; importers name the `nogc_*` copies |
| `src/lib/gc_sync_mut/tls/_TlsUtilities/text_ops.spl` | — | same |
| `src/app/_scratch_ed/main.spl` | — | scratch entry point |

A seventh, `src/compiler/50.mir/_MirLoweringExpr/literals.spl` (717 lines), was
deleted in the change that filed this.

## The first census was wrong in BOTH directions — method matters here

The first pass matched a part-file's **leaf name** against the leaf of every
`use` in `src/`. It reported five orphans. Every number in it was wrong, and the
two failure modes are worth recording because either one alone would have
produced a confident bad answer:

- **False positives from an `src/`-only importer scan.** It named
  `src/os/_QemuRunner/vm_process_lifecycle.spl` and `guest_evidence_contract.spl`
  as orphans. Both are imported — by `test/unit/os/vm_process_lifecycle_spec.spl`.
  A spec is a real consumer, so the import scan has to cover the whole repository
  even though the part-file enumeration is `src/`-only.
- **False negatives from leaf-name matching.** A leaf like `text_ops` or
  `archive` collides with unrelated modules, so an unimported file was marked
  imported by somebody else's `use`. Exact module paths are required.

Deriving those exact paths has two rules that are easy to miss, and getting
either wrong flips the answer:

- a numeric ordering prefix on a directory segment is dropped, so
  `src/compiler/50.mir/_MirLoweringExpr/literals.spl` is
  `compiler.mir._MirLoweringExpr.literals`;
- `src/lib/**` is reachable as `std.<rest>` (CLAUDE.md: "`use std.X` resolves
  here") and bare as `<rest>`, as well as the literal `lib.<rest>`. Missing those
  aliases made an intermediate revision call seven live stdlib part-files orphans.

## Why this is worth a record rather than a quiet cleanup

The deleted one cost six weeks of misreading. `literals.spl` defined 13
`impl MirLowering:` methods that a sibling also defined, was filed in 2026-08-08
as a duplicate-method defect, and was investigated as a load-ORDER question —
which copy wins. The answer was that neither did: the file was never loaded. That
investigation even ran a marker experiment whose result (0 fires versus 3) is
fully explained by orphaning, and read it as evidence about ordering.

Two further facts from that closure generalise to the whole class:

- **A dead copy absorbs half a fix.** Its `lower_dict_lit` and `lower_tuple_lit`
  carried the FULL rationale for two non-obvious fixes, while the live file had
  been abbreviated to "see the identical copy ... must stay in sync", with five
  references across three other files pointing readers at the file nothing compiled.
- **A dead file can stop compiling and nobody notices.** `sweep/seed.tsv` had
  recorded `literals.spl` as `compile failed`,
  `Undefined("undefined identifier: runtime_file_rename")`. That row sat there
  because nothing compiles the file, so nothing acted on it.

## `native_build.spl` — do not delete blind

Unlike `literals.spl`, this is not a whole-file duplicate. What is established:

- It defines 21 declarations. Seven, including the entry point `cli_native_build`,
  also exist in the live sibling `src/app/io/_CliCompile/compile_targets.spl`
  (1,516 lines), which IS imported.
- Its `cli_native_build` body is ~513 lines; the live one is a two-line delegator
  to `_cli_native_build`. The live implementation is not a copy of this file's.
- `_native_build_entry_closure` is defined here at line 256 **and** as `pub fn` in
  the live, imported sibling `native_build_closure.spl:271`, which is what
  `compile_targets.spl` and `parse_shard_main.spl` actually call.
- The two live halves have already diverged from it: `_nb_module_path_from_use`
  exists here and **not** in `native_build_closure.spl`.

The shape is a split completed in the importers but never finished by deleting the
original. Removal is very likely correct and worth 851 lines, but it needs the
dependent-surface sweep below plus a check that no live half still needs a helper
only this file defines.

## The dependent surface is the trap, not the deletion

Deleting `literals.spl` was behaviour-neutral by construction and still touched
nine other places, **none of which a search of `src/` would have found**: 9 rows
in `use_target_resolves_baseline.txt`, 3 in `raw_sffi_unsafe_baseline.tsv`, 3 in
`silent_fail_open_baseline.txt`, 1 each in `critical_wildcard_baseline.txt` and
`fail_open_baseline.txt`, an assertion in
`test/01_unit/compiler/mir/value_access_ownership_spec.spl`, a whole audit script
pinned to it plus its `guard_wiring_unwired_baseline.txt` row, and a data row in
`sweep/seed.tsv`. A baseline that no longer describes the tree is itself a FAIL
here, so leaving any of the first five would have broken those gates.

**Anyone deleting one of the remaining six must repeat that sweep over the whole
repository, not over `src/`.**

## Ratchet

`scripts/check/check-orphan-part-files.shs` freezes the six in
`scripts/check/orphan_part_file_baseline.txt` and fails any change adding a
seventh. Two-way, like the other ratchets here: a baselined entry that is no
longer an orphan — it became imported, or was deleted — is a STALE baseline and
also fails, since a baseline that no longer describes the tree is how a ratchet
silently stops ratcheting. Verdict is the last line of stdout, `PASS — <n>
part-file(s) checked, 0 new, 0 stale` / `FAIL` / `ERROR — nothing was checked`,
and a run that enumerated 0 part-files is an ERROR, never a pass. Measured on the
tree: `PASS — 238 part-file(s) checked, 0 new orphan(s), 0 stale baseline
entr(ies) (6 baselined)`.

`--selftest` runs first and is fatal, 8 fixtures, each pinning one thing that was
actually got wrong while writing it: an imported part-file must not be flagged; an
unimported sibling must be (the `literals.spl` shape exactly); a `50.mir`-style
numeric prefix must resolve to `mir`; a selective `use a.b.{X}` must count as
importing `a.b`; `src/lib` must resolve through the `std.` alias; a spec under
`test/` is an entry point and not a part-file; a tree with no part-files must
report 0 checked so the caller is forced to ERROR; and an empty offender list must
count 0 rather than the two-line string `0\n0` that `grep -c ... || echo 0`
produces, which had the guard reporting FAIL with an empty offender list.

A zero-bar was not an option: the six cannot be deleted blind, and a guard that is
red on `main` protects nothing.

## Known limit, stated rather than papered over

The guard sees direct imports only. `_initramfs_pack/support.spl` is imported
exactly once — by `archive.spl`, which is itself an orphan — so it is transitively
dead and the guard calls it live. Reachability from a real entry point, rather
than presence of any importer, would catch that class; it is not implemented.

## Related

- `duplicate_impl_method_definitions_silent_first_wins_2026-08-08.md` — the record
  this came out of, and the one deletion already made.
- `value_access_ownership_spec_never_executes_2026-09-18.md` — found in the same
  hour, same family: a guard that cannot run is indistinguishable from one that passes.
