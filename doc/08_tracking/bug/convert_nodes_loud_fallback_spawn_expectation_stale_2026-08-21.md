# convert_nodes_loud_fallback_spec: spawn example stale — bridge now has an EXPR_SPAWN arm

- **Date:** 2026-08-21
- **Spec:** `test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl` (3/4; failing: "records a parser error for a real spawn(...) call expression")
- **Status:** open, pre-existing (surfaced while re-running frontend specs for the grammar-registry cross-check work; that work touched neither the bridge nor EXPR_SPAWN)

The example asserts `parser_has_errors()` after parsing `spawn(w)`, i.e. that the FlatAst bridge still hits the loud fallback for tag 39. At HEAD `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1258` has a real `if tag == EXPR_SPAWN:` arm (verified with `git grep -n EXPR_SPAWN HEAD -- src/compiler/10.frontend/_FlatAstBridge/`), so the node converts cleanly and no error is recorded. The spec should be updated to assert the converted `Spawn` node instead (the STMT_STATIC_FOR sibling example in the same file still passes and remains a valid loud-fallback probe). Owner of the bridge lane should take it, since that tree is live.
