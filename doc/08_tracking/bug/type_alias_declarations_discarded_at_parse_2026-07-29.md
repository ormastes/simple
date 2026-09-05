# Bug: `type X = Y` alias declarations are discarded at parse time — nothing downstream can see them

- **Date:** 2026-07-29
- **Severity:** medium (blocks semantic-alias enforcement; silent semantic hole)
- **Area:** 10.frontend parser / arena / FlatAstBridge
- **Found by:** lane ALS1 (semantic-alias-registry) of the mission-critical robustness campaign — the lane STOPPED instead of building an always-empty registry.

## Symptom

The semantic_api checker's alias hook
(`src/compiler/35.semantics/lint/semantic_api/type_walk.spl:51-56`,
`semantic_api_resolve_alias`, called from `_sa_classify_leaf` at :154) is
fail-open with a gap comment "no alias registry exists". A registry cannot be
built: alias declarations never survive parsing, so MC-API rules (and any
future checker) can be evaded by aliasing a forbidden type.

## Root cause

`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:832-845`
(`parse_module_body`, the dispatcher feeding the arena `_FlatAstBridge`
consumes) handles `TOK_KW_TYPE` (kind 35) by literally skipping to newline:

```
elif par_kind_get() == 35:
    # Type alias: type X = Y -- skip it
    parser_advance()
    # Skip until newline
    ...
```

No name or aliased type is captured; no `decl_*` node is created;
`module_add_decl` is never called. Supporting evidence:

- No arena decl kind for aliases exists at all: zero hits for
  `decl_type_alias|DECL_TYPE_ALIAS|TypeAlias(` under
  `src/compiler/10.frontend/core/` (outside tokens/treesitter).
- `_FlatAstBridge` hardcodes empty:
  `convert_nodes.spl:217` (`flat_empty_module`) and
  `module_assembly.spl:648` (`parser_module_new(...)`) both pass
  `type_aliases: {}` — there is nothing in the arena to source it from.
- A separate, disconnected path DOES retain alias name+type:
  `10.frontend/treesitter/outline.spl` (`TypeAliasOutline`, populated via
  `treesitter.spl:106` / `outline.spl:871`) — but it feeds only
  `80.driver/driver_types.spl` / `compiler/treesitter.spl` / the Rust-side
  lint, never `_FlatAstBridge` or `35.semantics`.

## Fix direction (prerequisite chain)

1. New arena decl kind for type aliases + capture name/type in
   `parse_module_body` (replace the skip loop).
2. Thread through `_FlatAstBridge` into `module.type_aliases` (the field
   already exists and is hardcoded `{}`).
3. THEN build `semantic_api/alias_registry.spl` and close the fail-open hook
   (lane ALS1's original scope — resume it once 1-2 land).

## Note

Same defect family as the FlatAstBridge silent-NilLit fallback (fixed loud in
`147c80f4248`) and the arena tag lossiness A1 proved: the frontend silently
drops surface syntax, and downstream layers can neither see it nor detect the
loss.
