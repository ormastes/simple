# Bug: `type X = Y` alias declarations are discarded at parse time — nothing downstream can see them

**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

## Re-check 2026-09-13

- Status: RESOLVED (2026-09-13, prior lane) — verified, not newly authored

`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` no longer
skips `type X = Y` to newline. The `elif par_kind_get() == 35:` arm now
captures the name and aliased-type tag and calls
`module_add_decl(decl_type_alias(ta_name, ta_type_tag, 0))`, tagged inline as
"lane TAL1" for this bug id. `decl_type_alias` exists
(`10.frontend/core/_Ast/decl_nodes.spl:637`), and
`_FlatAstBridge/module_assembly.spl:1052,1195` threads the captured aliases
into `module.type_aliases` (a real `Dict<text, ParserTypeAlias>`, no longer
hardcoded `{}` — that hardcode survives only in `convert_nodes.spl:233`'s
`flat_empty_module`, which is correct for a module with no declarations at
all).

All three specs named in this fix's own comment/family are green on
`bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`
(symlinked from the shared main worktree), sha256 `3d120a6f9ab5`:

```
test/01_unit/compiler/frontend/type_alias_survives_parse_spec.spl  -> 3 examples, 0 failures
test/01_unit/compiler/frontend/type_alias_capture_spec.spl         -> 4 examples, 0 failures
test/01_unit/compiler/semantics/semantic_alias_registry_spec.spl   -> 10 examples, 0 failures
```

The last of those is the "Fix direction" step 3 registry this record asked
for (`semantic_api/alias_registry.spl`), also already landed. No new code
change needed; this record was stale relative to the tree.
