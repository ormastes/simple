# `semantic: variable LintDiag not found` — lint chain broken by two stale-snapshot clobbers (2026-08-21)

## Symptom
With a seed built from `origin/main` `348815b2e42`, any spec that loads the lint
chain fails, e.g.
`test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl`
-> `2 examples, 2 failures`, both `semantic: variable LintDiag not found`.
The 14:27 seed (`e73a0bec647`) passed the same spec.

## Cause — SOURCE side, not the seed
`git log e73a0bec647..348815b2e42 -- src/compiler_rust` has 39 commits, but none
of them is responsible. Both defects are dangling references left by
stale-snapshot clobbers; the older seed's late binding tolerated them on the
paths it took, the newer one resolves them eagerly.

1. `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:109-211` called
   `LintDiag.new(...)` / `LintRunResult.new(...)`. Those names were introduced
   by `3c9334600fa` (tool-side rename to dodge a collision with
   `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl`), but the class
   *definitions* in `_LintMain/config_and_model.spl:742,781` were rolled back to
   `Lint` / `LintResult` by the tree-wipe repair `ae55a746719`, and
   `traceability_and_assertions.spl` was corrected to match (pinned by
   `test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl`).
   `entry_and_fixes.spl` was the one file left behind, so it referenced two
   class names that exist nowhere in the tree.
2. Behind that, `src/compiler/35.semantics/lint/required_comment.spl:24` imports
   `source_may_contain_dangerous_keyword` from
   `src/compiler/10.frontend/core/dangerous_keywords.spl`. The function was added
   by `8c50d36609b` and had since been dropped from that file — a second
   dangling reference (`semantic: function source_may_contain_dangerous_keyword
   not found`), exposed only after defect 1 was fixed.

## Fix
- `entry_and_fixes.spl`: `LintDiag` -> `Lint`, `LintRunResult` -> `LintResult`
  (direction chosen by the existing pinned spec and the live class definitions).
- `dangerous_keywords.spl`: restore `fn source_may_contain_dangerous_keyword`
  verbatim from `8c50d36609b`.

## Evidence
| spec | before | after |
|---|---|---|
| `duplicate_typed_arg_signature_nil_miss_spec.spl` (reproduce) | 2 examples, 2 failures | 2 examples, 0 failures |
| `llvm_cross_module_global_symbol_spec.spl` (neighbor, +1 example) | 3/3 | 4/4 |
| `required_comment_admission_spec.spl` (neighbor, +1 example) | 2/2 | 3/3 |

Both neighbors gained an example that fails on the pre-fix tree, so the defect
class (a dangling cross-module name surviving a clobber) is now pinned in the
two files that actually carried it.
