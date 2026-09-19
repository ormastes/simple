# `simple lint` and `simple fix` disagree about which files they can analyse

**Status:** OPEN 2026-09-19
**Area:** `src/app/cli/lint_entry.spl` vs `src/compiler/90.tools/fix/main.spl`
**Found by:** measuring COLL diagnostic coverage vs fix coverage over the same
  52 files

## The discrepancy, on one file

```
$ bin/simple lint test/01_unit/compiler/30.types/simd_capabilities_extern_backing_spec.spl
error: semantic: string index out of bounds: index is 7628 but length is 7628
   (no findings of any kind)

$ bin/simple fix --dry-run test/01_unit/compiler/30.types/simd_capabilities_extern_backing_spec.spl
  1 fix(es) applied
  [COLL020] track membership in `seen_set` Dict instead of `.contains` on `seen`
```

Same file, same machine, same binary, same rule family. `lint` cannot get
through it; `fix` analyses it and finds a real O(n^2) dedup loop plus a
machine-applicable rewrite for it.

## Why

`fix` reaches the COLL rules through `collection_certain_fixes`, which parses
the source (`parse_module_silent_checked`) and runs `check_collection_patterns`
on the resulting arena. It never runs the semantic phase. `lint` runs the full
front end first, and the three aborts recorded in
`lint_semantic_string_index_out_of_bounds_aborts_whole_file_2026-09-19.md` and
`lint_other_whole_file_aborts_2026-09-19.md` all happen in or after that
phase. So `fix` is more robust than `lint` by accident of taking a shorter
path, not by design.

## Why it needs deciding rather than leaving

A user gets different answers from two commands about the same file, and
neither answer says the other exists. Both directions are defensible and they
have opposite consequences:

- **`lint` should survive**: a rule that needs only the parse tree should not
  be lost because an unrelated semantic check failed. This is the better
  outcome for coverage — 7 of the 54 genuinely-quadratic dedup sites in the
  measured corpus are unreportable purely because of this.
- **`fix` should be failing too**: if the semantic phase genuinely cannot
  make sense of the file, a machine-applicable REWRITE derived from a parse
  the compiler could not finish analysing is the more dangerous of the two
  operations, not the safer one.

The second reading deserves weight here specifically, because this lane spent
four rounds establishing that the COLL Certain fix must PROVE safety before
rewriting. The COLL proofs are purely syntactic and do not consult semantic
information, so nothing measured says the rewrite is wrong on such a file —
but "the front end could not analyse this and we rewrote it anyway" is not a
position anyone chose, and nobody has checked what it implies for the other
fix providers that share the `simple fix` door.

## Not in scope of the lane that found it

Recorded, not resolved: which way this should go is a decision about the tool's
contract, not a bug with an obvious fix, and it affects every rule rather than
the COLL family.
