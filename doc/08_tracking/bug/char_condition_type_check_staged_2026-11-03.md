# char_condition_type_check_staged_2026-11-03

- **Status:** open — staged; warning stage DONE, error promotion BLOCKED
- **Priority:** P2
- **Platform:** shared dependency (not macOS-exclusive)
- **ADR:** `doc/04_architecture/adr/ADR-005-text-index-yields-char.md`
  § "Char truthiness and construction", § "Additional staging rows"
- **Sibling:** `char_literal_lexer_switch_staged_2026-11-03` (separate owner)

## Defect

A `char` has no truthiness (ADR-005): `if c:`, `while c:`, `not c`, and
`c and x` / `c or x` must be a type error; write `c != '\0'`.

## Stage 1 — warning (landed, verified 2026-11-04)

- Checker: `src/compiler/20.hir/exhaustiveness/char_condition.spl`
  (`W-CHAR-CONDITION`, mode resolution
  `SIMPLE_SAFETY_PROFILE=critical|verified` > `SIMPLE_CHAR_CONDITION=error` >
  default warn), called from HIR lowering at if/elif/while
  (`hir_lowering/statements.spl`, `_Expressions/expression_core.spl`), `not`,
  and `and`/`or` operands. Landed in `51ab847392b`.
- Runtime fail-closed: seed `RuntimeValue::truthy()` on a char tag does not
  return a bool (`src/compiler_rust/runtime/src/value/mod_tests.rs:590`).
- Evidence: `bin/simple test test/03_system/app/compiler/feature/char_condition_spec.spl`
  on `release100-7a0e6fe516f-20261031` (macOS arm64) at release/1.0.0
  `fb18c371767` -> `outcome=OK executed=9 passed=9 failed=0`.
- Seed checker: not added. The seed is bootstrap-only (CLAUDE.md) and has no
  static condition-type pass; the runtime fail-closed path covers it, and the
  self-hosted checker is the enforcing layer.

## Stage 2 — error by default (BLOCKED)

ADR-005 promotion trigger: default flips from warn to error only once
Windows, macOS **and** Linux each have a working self-hosted Simple binary
(same staging as non-exhaustive match). Blockers as of 2026-11-04:

- macOS: no admitted self-hosted build on release/1.0.0 (bootstrap lane owns
  it; Stage 3 blocked, see `arm64_macos_audit_20261103/current_inventory.md`).
- Windows/Linux: not verified in this lane.

Flip recipe when unblocked: change the default in `cc_mode_resolve`
(`char_condition.spl`) to error, update the spec's default-mode expectation,
and close this row. No code change is safe before then: the frozen stage2
compiles compiler sources that may still contain char conditions.
