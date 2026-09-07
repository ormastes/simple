# `s{...}` set literal is unparsed — seed has no production, self-hosted frontend has half

**Date:** 2026-09-06
**Status:** OPEN (feature gap, not a defect in landed code)
**Severity:** P3 — the set TYPE and all its OPERATIONS now work; only the literal
sugar is missing, and `Set.from([...])` is a complete substitute.

## Symptom

`s{1, 2, 3}` does not parse on the deployed compiler:

```
$ bin/simple run /tmp/p1.spl        # fn main(): val nums = s{1, 2, 3}
error: compile failed: parse: in "/tmp/p1.spl":
       Unexpected token: expected expression, found Comma
```

The error is misleading: `s{` is not recognised as a literal prefix, so `s`
lexes as an identifier and `{1` opens a block; the first `,` is then
unexpected. Nothing reports "set literal unsupported".

## Where the feature actually stands

This is not a greenfield gap — it is a half-built feature whose two halves are
in different compilers.

**Rust seed (`src/compiler_rust`) — the DEPLOYED binary, nothing at all:**
`grep -rn "SetLit" src/compiler_rust --include=*.rs` returns **0 hits**. No
token, no AST node, no production.

**Pure-Simple compiler (`src/compiler/**.spl`) — everything DOWNSTREAM exists,
nothing upstream:**

| Layer | File | State |
|---|---|---|
| AST node | `10.frontend/parser_types_expr.spl:426` | `SetLit([Expr])` declared |
| Token | `10.frontend/lexer_types.spl:190` | `SetLitStart` declared |
| HIR node | `20.hir/hir_definitions.spl:580` | `SetLit(elements, elem_type)` |
| HIR lowering | `20.hir/hir_lowering/_Expressions/expression_core.spl:352` | implemented |
| Type inference | `30.types/type_infer/inference_expr.spl:448` | implemented |
| MIR lowering | `50.mir/_MirLoweringExpr/literals.spl:600` | implemented |
| Config | `src/lib/nogc_sync_mut/src/config.spl:158-166` | `default_set()`, `prefix: "s"` |
| **Parser production** | — | **MISSING — nobody constructs `ExprKind.SetLit`** |
| **Lexer production** | — | **MISSING — nobody emits `SetLitStart`** |

`SetLitStart` sits in `10.frontend/lexer_types.spl`, which is **not** the live
lexer. The live path is
`frontend.spl:94 parse_full_frontend_with_scope` → `flat_ast_bridge` →
`core/lexer.spl` + `core/parser.spl` (flat pool, integer tags) →
`_FlatAstBridge/convert_nodes.spl`. `core/lexer_types.spl` has no `SetLitStart`,
and there is no `EXPR_SET_LIT` flat-pool tag anywhere
(`grep -rn EXPR_SET_LIT src/compiler` → 0 hits).

## Why it was not implemented in this lane

Implementing it in the pure-Simple frontend would resolve **zero** observable
TODOs: `bin/simple test` runs the Rust seed, so a self-hosted-only production
cannot be reached from any spec until a bootstrap redeploys. The work is also
wide for a P3 sugar — a new `core/lexer_types.spl` token, a `core/lexer.spl`
adjacency rule, a core-parser production, a new `EXPR_SET_LIT` flat tag, the
converter arm in `convert_nodes.spl`, the four tag-walks in
`desugar/placeholder_lambda.spl` (191/490/641/806) and the dispatch in
`70.backend/backend/compile_c_entry.spl:145` — six-plus shared-frontend files.

## Unblock condition

Either lane resolves it; the seed lane is the one that makes it observable.

1. **Seed lane (makes `s{}` usable):** add the `s` + adjacent `{` prefix rule to
   the seed lexer and a set-literal production to the seed parser, rebuild, and
   redeploy `bin/release/<triple>/simple`.
2. **Self-hosted lane (needed for bootstrap parity):** the six-plus files above.

No collision risk was found for the `s` + `{` adjacency rule: across `src/` and
`test/`, every non-comment `s{` occurrence is inside a string literal
(`src/lib/scv/event_source.spl:22`, `nogc_async_mut/mcp/diag_edit_tools.spl:233`),
where the lexer is already in string context.

## Related

- `test/03_system/feature/usage/set_literal_spec.spl` — the set TYPE and all five
  operators are now exercised against the real `Set<T>` (13/13). The inline
  `# val nums = s{1, 2, 3}  # TODO: Set literal syntax not yet implemented`
  comments are deliberately retained and remain accurate.
- `test/03_system/feature/usage/custom_literal_spec.spl` — sibling spec, still on
  its own local text-matching harness (`is_custom_set_literal` compares
  `starts_with("s{")`). Next candidate once the literal lands.
- `src/lib/nogc_sync_mut/src/set.spl` — `Set<T>` was unusable until 2026-09-06;
  its `Map<T, bool>` index needed `T: Hash` and `Map` aborts on `i64` keys.
  Membership is now an O(n) scan of `items`. Restoring a hash index depends on
  fixing `Map` for primitive keys, which is a separate open item.
