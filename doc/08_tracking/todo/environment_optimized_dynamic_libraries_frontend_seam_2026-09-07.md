# TODO: Environment variant frontend seam integration

**Status:** Open — concurrent ownership
**Owner:** frontend integration lane after current parser work is reconciled
**Final reviewer:** Astra/highest-capability architecture reviewer
**Affected criteria:** REQ-008, REQ-009, REQ-013; AC-5, AC-6, AC-8

## Current blocker

The shared frontend neighborhood contains untracked work owned by other active
sessions, including `src/compiler/10.frontend/core/lexer_tape.spl`,
`src/compiler/10.frontend/structural_adapter/`, interpreter canonical adapters,
and their tests. Integrating `FrontendFacetV1` into
`src/compiler/10.frontend/core/frontend.spl` before that lane stabilizes risks
folding or invalidating unrelated parser work.

The deeper API blocker is also explicit: the lexical bridge returns
`SimpleCoreLexerParseResult` with `oracle_verified=false`, but the full frontend
still returns mutable-global-state booleans or `ParserModule`. Result-returning
full parse APIs named by concurrent tests are not implemented. The canonical
structural runtime covers only a toy lexical program; SDN and sosh retain
separate result models.

## Resume procedure

1. Confirm the active parser session has finished or explicitly transferred ownership.
2. Inspect `git status --short -- src/compiler/10.frontend src/app/interpreter test/01_unit/compiler/frontend` and identify the retained owner/diff.
3. Reconcile the legacy adapter with the actual lexer/structural seam; preserve reset, append, isolated error state, interpolation, placeholder transformation, diagnostics, and spans.
4. Produce length-prefixed normalized token/span/node/diagnostic digests from
   ordered full results for Simple, SDN, and sosh, binding grammar/actions/schema
   and implementation generations. Do not use the structural runtime's 32-bit
   lexical hash as AST identity.
5. Run the focused reference-mode frontend tests once with a provenance-admitted self-hosted Stage-4 CLI.

## Retained inputs

- `FrontendFacetV1` contract: `src/lib/nogc_sync_mut/composition/environment_variants/contracts_v1.spl`
- Architecture/design: `doc/04_architecture/compiler/environment_optimized_dynamic_libraries.md`, `doc/05_design/compiler/environment_optimized_dynamic_libraries.md`
- Concurrent parser files remain untouched by this lane.

## Unblock condition

Ownership is transferred or the concurrent parser lane becomes clean/stable,
and a reviewer confirms the integration diff preserves both workstreams.
