# Scoped Visibility Lost In Flat AST Bridge

## Summary

This bug was fixed on 2026-04-17.

`pub(peer)` / `pub(up)` / other scoped visibility forms originally parsed in
the pure Simple frontend, but one frontend bridge still collapsed them to a
boolean `decl_is_pub` flag and reconstructed declarations as only
`Visibility.Public` or `Visibility.Private`.

That made the feature look like "the statement/syntax is not working" even
though the parser-side visibility model already supported scoped forms.

## Classification

- Status: fixed
- Severity: P1
- Area: pure Simple frontend bridge
- Type: propagation bug with parser-visible symptoms

## Root Cause

`src/compiler/10.frontend/flat_ast_bridge.spl` rebuilt declaration visibility
from `decl_is_pub[idx]` instead of carrying the declared visibility through the
flat AST bridge.

The original affected sites included:

- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:335)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:377)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:460)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:474)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:487)

The original bridge logic repeatedly did this:

```simple
visibility: if decl_is_pub[idx] != 0: Visibility.Public else: Visibility.Private,
is_public: decl_is_pub[idx] != 0,
```

That caused:

- `pub(peer)` is downgraded to `public` or `private`
- `pub(up)` is downgraded to `public` or `private`
- `pub(package)` / `pub(friend)` / `internal` cannot survive this path either
- field visibility is hardcoded to `Visibility.Private` in at least one struct path

## Why It Looks Like A Parsing Bug

From a user perspective the syntax is accepted, but the resulting declaration
behavior does not match the written source. That usually looks like a parser
bug. More precisely, this is a frontend parsing-propagation bug:

1. parser/tree-sitter side understands scoped visibility
2. flat representation drops the detail
3. later stages only see public/private

## Resolution

The pure Simple frontend now preserves declared visibility end-to-end through
the active parser and flat AST bridge.

Implemented changes:

1. `src/compiler/10.frontend/core/parser_decls.spl` parses `pub`, `pub(peer)`,
   `pub(up)`, `pub(friend)`, `pub(package)`, and `pri` on the active parser
   path.
2. `src/compiler/10.frontend/core/ast.spl` stores canonical declaration
   visibility as `decl_visibility`, with `decl_is_pub` retained as a derived
   compatibility field.
3. `src/compiler/10.frontend/flat_ast_bridge.spl` converts from
   `decl_get_visibility_text(...)` instead of reconstructing from
   `decl_is_pub`.
4. downstream pure Simple readers were aligned so scoped visibility is not
   treated as plain public in backend/export and lint paths.

## Expected Behavior

The pure Simple frontend should preserve `Visibility` end-to-end through the
flat AST bridge so downstream semantics, query, LSP, and docs see the same
declared visibility that the source expressed.

## Final Behavior

The original failures were:

1. Bare `pub` declarations were previously rejected by the core parser path
   because `parse_module_body()` did not dispatch `TOK_KW_PUB`.
2. Scoped visibility syntax is still flattened back to bool-like visibility in
   `flat_ast_bridge.spl`.

Both issues are now fixed on the active pure Simple path.

## Verification

- `test/unit/compiler/parser/flat_ast_pub_decl_spec.spl`
- `test/unit/compiler/parser/treesitter_visibility_spec.spl`
- `test/integration/app/query_visibility_surfaces_spec.spl`
- `test/integration/app/query_visibility_workspace_symbols_spec.spl`
- `test/integration/app/lsp_query_visibility_symbols_spec.spl`

## Regression Targets

- `pub(peer) fn helper(): ...`
- `pub(up) fn helper(): ...`
- `pub(package) fn helper(): ...`
- struct field visibility through flat bridge

## Notes

This is distinct from earlier runtime Rust parser limitations such as
`parser_003`. This bug was in the pure Simple frontend path and is now closed.
