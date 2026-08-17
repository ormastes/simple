# HIR flat-AST impl lowering lost `current_method_self_symbol_id` save/set/restore

- **Status:** RESOLVED 2026-08-17 — the deleted save/set/restore triple was
  restored in `module_lowering.spl`'s flat-AST impl loop (save
  `previous_impl_self_symbol_id` before the loop, set
  `impl_owner_symbol.id` when valid, restore after), mirroring the intact
  sites in `declaration_lowering.spl:634-649` and
  `trait_impl_lowering.spl:204-231`. Verified: `grep -c
  current_method_self_symbol_id` in the file is back to **3** (was 0),
  matching the pre-regression count at `83d21f1808~1`. Full effect lands with
  the next bootstrap deploy (this path only runs under `SIMPLE_BOOTSTRAP`).
  **Regression specs** (both PASS post-fix; repro asserts the exact triple
  that was absent pre-fix, so it is RED against the regressed source):
  repro `test/01_unit/compiler/hir/impl_lowering_self_symbol_id_spec.spl`;
  generalization (same defect class across all three method-entering lowering
  paths + field existence)
  `test/01_unit/compiler/hir/method_self_context_save_restore_spec.spl`.
  Both mirrored to `test/unit/compiler/hir/`.
- **Found:** 2026-08-11, during skeptical review of landed refactor commits
- **Introduced by:** `83d21f1808` ("refactor(compiler): consolidate 4-way duplicated
  module-name-from-path derivation") — collateral, unrelated to that commit's stated scope
- **File:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
  (flat-AST / `SIMPLE_BOOTSTRAP` impl-block lowering path)

## What happened

`83d21f1808` is titled and described as a pure consolidation of the four
duplicated `*_module_name_from_path` copies into
`src/compiler/00.common/module_path_naming.spl`. That part of the diff is
behaviour-preserving. But the same commit also carries three unrelated deletions
in `module_lowering.spl`'s impl-block lowering loop:

```
-            val previous_impl_self_symbol_id = self.current_method_self_symbol_id
             if impl_owner_symbol.is_valid():
                 self.current_method_self_type = Some(...)
-                self.current_method_self_symbol_id = impl_owner_symbol.id
...
             self.current_method_self_type = previous_impl_self_type
-            self.current_method_self_symbol_id = previous_impl_self_symbol_id
```

Counts: `git show 83d21f1808~1:...module_lowering.spl | grep -c
current_method_self_symbol_id` = **3**; at `origin/main` = **0**. The removal is
still live.

## Why it matters

`current_method_self_symbol_id` is not decorative. It is initialised to `-1`
(`hir_lowering/types.spl:230`) and is the sole input to the `self.<field>` type
resolution fast path:

```
src/compiler/20.hir/hir_lowering/expressions.spl:229
    if self.current_method_self_symbol_id >= 0:
        ...
            return self.field_type_for_owner_raw(self.current_method_self_symbol_id, field_name)
```

The two other lowering paths that enter method bodies still set it —
`_Items/declaration_lowering.spl:569-586` and `_Items/trait_impl_lowering.spl:200-229`
— using exactly the save/set/restore shape that was deleted here. Only the
flat-AST impl path in `module_lowering.spl` lost it.

**Concrete failure shape:** lowering an `impl Foo:` block through the flat-AST
bridge (the `SIMPLE_BOOTSTRAP=1` path) leaves `current_method_self_symbol_id` at
`-1` (or, worse, at whatever a previously-lowered *enclosing* declaration left
behind, since the restore was also deleted). A method body containing
`self.<field>` then either skips `field_type_for_owner_raw` entirely and falls
back to a weaker/unknown field type, or — in the stale-value case — resolves the
field against the WRONG owner symbol, silently typing `self.x` as some other
struct's `x`. The `current_method_self_type` half of the pair is still saved and
restored, so the two now disagree, which is the classic shape of a
type-resolution bug that only shows up in bootstrap/native lowering and not in
the interpreter spec corpus.

## Also in the same commit (already healed, recorded for the record)

`83d21f1808` additionally reverted `src/lib/common/text_advanced.spl`'s
`escape_json` from the shared `std.text.escape_json` delegation back to the
5-`replace()` chain that does not escape C0 control characters, and **deleted**
`test/01_unit/lib/common/text_advanced_escape_json_spec.spl` (the regression
guard for exactly that). Both were restored by a later commit — at `origin/main`
the spec exists and the delegation is back — so this half needs no action. It is
noted here because it is the same stale-base-snapshot signature as the
`current_method_self_symbol_id` loss, and it is evidence that `83d21f1808` was
landed from a stale working copy rather than being the scoped refactor its
message claims.

## Suggested resolution

Restore the three lines in `module_lowering.spl`'s impl-block loop, matching the
still-correct shape in `declaration_lowering.spl:569-586`. Do **not** revert
`83d21f1808` wholesale — its module-path-naming consolidation is good and is now
pinned by `test/01_unit/compiler/common/module_path_naming_spec.spl`. A human
should confirm whether the removal was accidental (stale snapshot) or an
intentional change made elsewhere, before restoring.
