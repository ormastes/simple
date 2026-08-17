# Bug: `type X = Y` alias declarations are discarded at parse time — nothing downstream can see them

- **Status (2026-08-17, lane A re-verification): ALREADY FIXED IN-TREE — closeable.**
  Classified by CONTENT, not by commit ancestry.
  - `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:1374-1403` no
    longer skips `TOK_KW_TYPE` (kind 35): it captures the alias name, parses the
    aliased type via `parser_parse_type()`, and calls
    `module_add_decl(decl_type_alias(...))`.
  - `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:820-830` consumes
    arena tag `17` and populates `type_aliases[ta_name] = ParserTypeAlias(...)`;
    the hardcoded `{}` at `module_assembly.spl:172` is now only the initial value.
  - `convert_nodes.spl:230` still hardcodes `type_aliases: {}`, but that is
    `flat_empty_module` (the empty-module constructor), not the populated path.
  - Item 3 of the fix chain below (`semantic_api/alias_registry.spl` and closing
    the fail-open hook in `35.semantics/lint/semantic_api/type_walk.spl`) is
    **still open** — this bug's own scope (items 1-2) is done.

  Evidence specs (both drive the pure-Simple frontend via
  `parse_and_build_module`, so they exercise the `.spl` parser even though the
  spec body runs interpreted):
  - `test/01_unit/compiler/frontend/type_alias_survives_parse_spec.spl` (reproducing)
    — `Results: 3 total, 3 passed, 0 failed`
  - `test/01_unit/compiler/frontend/module_surface_syntax_not_dropped_class_spec.spl`
    (class detection: any module-level surface form silently dropped by a
    skip-to-newline dispatcher branch) — `Results: 5 total, 5 passed, 0 failed`

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
