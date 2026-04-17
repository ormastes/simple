# Scoped Visibility Lost In Flat AST Bridge

## Summary

`pub(peer)` / `pub(up)` / other scoped visibility forms appear to parse in the
pure Simple frontend, but one frontend bridge still collapses them to a
boolean `decl_is_pub` flag and reconstructs declarations as only
`Visibility.Public` or `Visibility.Private`.

This makes the feature look like "the statement/syntax is not working" even
though the parser-side visibility model already supports scoped forms.

## Classification

- Status: open
- Severity: P1
- Area: pure Simple frontend bridge
- Type: propagation bug with parser-visible symptoms

## Root Cause

`src/compiler/10.frontend/flat_ast_bridge.spl` rebuilds declaration visibility
from `decl_is_pub[idx]` instead of carrying the full `Visibility` enum through
the flat AST bridge.

Affected sites include:

- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:335)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:377)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:460)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:474)
- [flat_ast_bridge.spl](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge.spl:487)

The bridge currently does this shape repeatedly:

```simple
visibility: if decl_is_pub[idx] != 0: Visibility.Public else: Visibility.Private,
is_public: decl_is_pub[idx] != 0,
```

That means:

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

## Expected Behavior

The pure Simple frontend should preserve `Visibility` end-to-end through the
flat AST bridge so downstream semantics, query, LSP, and docs see the same
declared visibility that the source expressed.

## Actual Behavior

Scoped visibility syntax is parsed upstream but flattened back to bool-like
visibility in `flat_ast_bridge.spl`.

## Recommended Fix

1. Extend the flat declaration representation to carry the full visibility enum
   instead of only `decl_is_pub`.
2. Update `flat_ast_bridge.spl` to use that full value directly.
3. Keep `is_public` as a derived compatibility field from `visibility.is_public()`.
4. Add a regression test that proves `pub(peer)` and `pub(up)` survive the flat
   AST bridge unchanged.

## Regression Targets

- `pub(peer) fn helper(): ...`
- `pub(up) fn helper(): ...`
- `pub(package) fn helper(): ...`
- struct field visibility through flat bridge

## Notes

This is distinct from earlier runtime Rust parser limitations such as
`parser_003`. The current issue is in the pure Simple frontend path.
