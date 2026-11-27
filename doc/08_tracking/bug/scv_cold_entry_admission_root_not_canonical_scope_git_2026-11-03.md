# SCV cold-entry admission: root-not-canonical, scope-unsupported, non-git root, missing default roots

Status: fix-implemented-verification-pending (needs a stage3 run on a worktree to prove 1).

1. `frozen cold entry rejected: root-not-canonical` for `src/` entries: the admission compared the
   caller's root spelling to `rt_path_absolute(root)` byte-for-byte; on NTFS a case-only difference
   (drive letter / directory casing from a worktree cwd) is the same directory. Now an ASCII
   case-only difference is accepted on Windows (`phase_compatibility_spelling_equivalent_v1`); the
   admitted spelling is still the realpath. Symlink/junction/other differences still reject.
2. `source-inventory-scope-unsupported`: reason string unchanged (scripts match it); the message now
   names the checkout root the entry and --source dirs must live under.
3. Non-git root: decision = clear diagnostic, not filesystem inventory (the whole inventory is
   `git ls-files` based). New reason `source-inventory-root-not-git` with the remedy.
4. Missing DEFAULT --source roots (`src/os`, `src/plugins`) are skipped with an `SCV-W-ADMISSION`
   warning. DECISION: an explicitly requested --source root that is empty or missing stays the hard
   error `source-inventory-root-empty`.

Spec: test/01_unit/app/compiler_entrypoint/scv_entry_admission_spec.spl.
Filed separately (not fixed here): two concurrent builds on one root can fail cold HIR snapshot
admission with `snapshot-open-provenance-invalid` (src/lib/scv/compile_snapshot.spl:234).
