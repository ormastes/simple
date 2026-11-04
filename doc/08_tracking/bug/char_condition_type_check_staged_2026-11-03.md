# char_condition_type_check_staged_2026-11-03

- **Status:** fix-implemented-awaiting-gate — warning default + error mode done; default flip waits on the ADR-005 gate
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

Flip recipe when unblocked (single switch point, 2026-11-04): in
`src/compiler/20.hir/exhaustiveness/char_condition.spl` change
`pub fn cc_default_mode() -> text: "warn"` to `"error"`, then update the
spec's `cc_default_mode()`/default-mode expectations and close this row.
Gate condition: an admitted self-hosted Simple binary on Windows, macOS and
Linux (ADR-005). No code change is safe before then: the frozen stage2
compiles compiler sources that may still contain char conditions.

## Stage 1.5 — error path + flip-ready gate (2026-11-04)

- Error mode emits `E-CHAR-CONDITION` as a fatal lowering error (warn mode
  keeps `W-CHAR-CONDITION` as a recovered warning); both carry the site
  `line:col` and a fix-it `help: compare explicitly, e.g. c != '\0' or c == 'a'`
  (`cc_message`). `SIMPLE_CHAR_CONDITION=warn` is honoured explicitly, so after
  the flip it is the opt-out (critical/verified profiles still force error).
- Default lives only in `cc_default_mode()`.
- Seed side: still not added, for the reason above (would need a second static
  condition-type pass in the bootstrap-only seed; runtime fails closed).
- Evidence: `char_condition_spec.spl` -> `outcome=OK executed=16 passed=16
  failed=0` (warn and error modes for if/elif/while/not/and/or, default-mode
  gate, message/hint) on `/Users/ormastes/.local/share/simple-seeds/release100-7a0e6fe516f-20261031/simple` at release/1.0.0 base `5cc998f2043`.
