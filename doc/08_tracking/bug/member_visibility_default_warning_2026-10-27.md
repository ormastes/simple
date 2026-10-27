# Member visibility enforcement ships as a default warning (workaround)

Tag: `# @workaround bug=member-visibility-default-warning-20261027` in
`src/compiler/20.hir/hir_lowering/_Expressions/member_visibility_check.spl`.

HIR now checks imported-composite field reads and aggregate construction
(parent bug: `member_visibility_enforcement_not_wired_into_hir_2026-10-26.md`).
The compiler's own sources contain thousands of cross-module reads of non-pub
fields, so by default the verdict is a `W-HIR-VIS-001` warning
(file:line + "mark the field `pub` / `pub(package)`"), deduped per HirLowering
session. `SIMPLE_ENFORCE_MEMBER_VISIBILITY=1` (or `member_visibility_strict_force`
in a spec) makes it an error.

## Removal plan
1. Collect W-HIR-VIS-001 over a self-host lowering sweep.
2. Add `pub` / `pub(package)` to every offending field.
3. Delete the default-warning path and the env/force toggle; make the check an error always.
4. Drop the `@workaround` tag and this record.

DB reconciliation pending: bug DB entry for member-visibility-default-warning-20261027 not yet added.
