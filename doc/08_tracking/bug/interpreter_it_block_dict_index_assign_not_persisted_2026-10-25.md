# Interpreter: `dict[key] = v` inside an `it` block does not persist into a module-level `Dict`

**Status:** OPEN
**Filed:** 2026-10-25 (found while landing BSM P5, PR #4804)
**Severity:** P3 — silent wrong result in test code; a helper-function workaround exists.
**Binary:** deployed `bin/simple` = Rust seed (seed WARNING banner), Windows 11.

## Symptom

In `test/01_unit/lib/mem/global_dataset_spec.spl`, a module-level
`var _rc: Dict<text, i64> = {}` written directly from an `it` block body:

```simple
it "pins an entry":
    _rc["k"] = 2          # not visible to the fake RcPort afterwards
```

was not observed by a module-level function reading `_rc["k"]` later in the
same test. Routing the write through a module-level helper persists it:

```simple
fn _set_rc(key: text, value: i64):
    _rc[key] = value
it "pins an entry":
    _set_rc("k", 2)       # visible
```

Colon-blocks are scopes, not closures (owner ruling 2026-09-27,
`.claude/rules/language.md`), so an `it` body may assign an enclosing `var`;
plain `var x = ...` reassignment in `it` bodies works. The failing form is
specifically the **index-assignment** `dict[key] = v` on a module-level dict
from inside the colon block.

## Where to look

Seed interpreter index-assignment path for `Expr::Index` targets when the base
is a module global reached from a `MoveMode::ColonBlock` body — likely the
write lands on a copied dict handle rather than the global slot (compare with
the helper-function path, which resolves the global directly).

## Workaround in tree

`test/01_unit/lib/mem/global_dataset_spec.spl` uses the `_set_rc` helper.
Do NOT normalise this pattern elsewhere; fix the interpreter or reproduce with
a 5-line spec and attach it here.

## Not verified

Whether the pure-Simple interpreter and native codegen share the defect (only
the Rust seed was run), and whether array index-assignment (`arr[i] = v`) is
affected.
