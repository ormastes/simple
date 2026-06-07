# Feature: accessor-fix-tooling-completion

## Raw Request
$sp_dev   sync gh again and find accesor_fix_tooling_completion_plan. and compelete it. and check lsp and treesitter sanity, clear 111 warnings about field

## Task Type
code-quality

## Refined Goal
Complete the accessor field-access tooling plan by proving the stale 111 ACC001 field/accessor warnings are cleared and the LSP and Tree-sitter sanity lanes still pass.

## Acceptance Criteria
- AC-1: `doc/03_plan/compiler/accessor_field_access/accessor_fix_tooling_completion_plan.md` is found and updated with completion evidence.
- AC-2: The accessor-fix dry run reports zero remaining safe wrapper removals or call rewrites.
- AC-3: A full lint sweep over the requested repository roots reports zero `ACC001` diagnostics and zero literal `field access` warning text.
- AC-4: Focused LSP specs for code actions, workspace edits, capabilities, and diagnostics pass.
- AC-5: Focused Tree-sitter parser/lexer/token/tree specs pass.
- AC-6: Accessor/field-access regression specs pass.
- AC-7: The repository is synced to GitHub without absorbing unrelated dirty work from the shared checkout.

## Scope Exclusions
- Do not rework unrelated lint warnings that are not `ACC001` or field-access warnings.
- Do not absorb the dirty/conflicted shared checkout into this lane.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: code-quality).
