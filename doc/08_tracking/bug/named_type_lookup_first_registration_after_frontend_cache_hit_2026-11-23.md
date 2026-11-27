# Named-type registry loses module ownership after a frontend cache HIT (`named_type_modules` not round-tripped)

- **ID:** named_type_lookup_first_registration_after_frontend_cache_hit_2026-11-23
- **Priority:** P4 (latent; no observable miscompile found on the current pipeline)
- **Status:** fixed (2026-11-25) — `flat_type_pools_restore` now rebuilds `named_type_modules` to
  `named_type_names.len()` after layout-owner validation, and `scripts/check/check-flat-ast-codec-complete.shs`
  explicitly documents the exclusion.
- **Found by:** review of PR #10933 while ruling out the `named_type_modules` lead for
  `stage3_surface_build_av_items_spl_warm_frontend_cache_2026-11-22.md` (section
  "`named_type_modules` not encoded").
- **Branch read:** `origin/release/1.0.0` at `3b2c8d8959c`.

## Symptom (hypothesised)
After a flat-AST frontend cache HIT, `named_type_modules` is empty, so the parser's named-type registry no
longer knows which module registered each row. The suspicion was that `named_type_find` would then pick the
FIRST registration of a bare type name instead of the current module's own declaration, so two modules that
declare the same type name could resolve to the wrong one only on a warm cache (a cache-dependent
miscompile / type error). On reading, that exact shape is not reachable through the cache (below); a
narrower divergence is, and it is currently harmless.

## Mechanism (file:line, `src/compiler/10.frontend/core/types.spl`)
- `:801` `var named_type_modules: [text] = []` — per-row declaring module; `:802` `named_type_current_module`.
- `:807-810` `named_type_module_at` returns `""` past the array end.
- `:812-836` `named_type_register`: an existing row whose module differs from the current one AND that has a
  layout (`named_type_fields(existing).len() > 0`) is treated as foreign, and a NEW owner row is appended.
- `:866-878` `named_type_find`: current module's own row first, else the first row with that name.
- `:1901` per-parse reset sets it to `[]` (with every other registry pool).
- `:2044-2046` `flat_type_pools_dump` encodes `named_type_names/arguments/layout_owners`, not `modules`.
- `:2210-2211` `flat_type_pools_restore` decodes the names and sets `named_type_modules = []`.
- `scripts/check/check-flat-ast-codec-complete.shs` reports it:
  `named_type_modules(not-encoded,not-decoded)`, one of 5 offenders (`expr_extra`, `expr_i_val`,
  `expr_s_val`, `par_error_records` are the other four), so encoding it alone would NOT turn that gate green.

## Reachability
1. **The blob is single-module.** Both the MISS store path (`_FlatAstBridge/module_assembly.spl:1864`
   `reset_all_pools()` then `parser_init_with_path`) and the HIT path (`:1740-1741`, same pair, then restore
   at `:1747`/`:1750`) start from empty pools. Every owner row in a blob was registered under that one file's
   path; instance rows from `named_type_apply` (`:844-858`) never get a module of their own even on a fresh
   parse (they read `""` through the padding at `:833-834`). So a restored registry never holds two modules'
   declarations of one name, and the "first registration" fallback of `named_type_find` returns the same row
   the module-aware lookup would (the owner is always registered before its instance rows). **The reviewer's
   two-modules shape cannot arrive through the cache.**
2. **The registry IS read after a hit.** `named_type_current_module` is the file path (set by
   `parser_init_with_path`, `core/parser.spl:486`, before the restore). The bridge re-parses generic
   type-parameter bound/default text: `_FlatAstBridge/convert_nodes.spl:2686-2692`
   (`lex_init_with_path(type_text, "")`, `parser_parse_type()`), which calls `named_type_find`
   (`core/parser.spl:1078, 1204, 1258, 1318`), `named_type_register` (`:1260, 1316, 1336`) and
   `named_type_apply` (`:1200`).
3. **The one real divergence:** after restore every row reads module `""` while the current module is the
   path, so `named_type_register(name, ...)` on a name that already has a layout appends a duplicate owner row,
   where the miss path would return the existing row. From the bound re-parse this is reachable only through
   - `named_type_apply` for `AdaptiveMap` / `AdaptiveSet` (`parser.spl:1199-1200`) in a file that itself
     declares that type with fields, or
   - `any` -> `named_type_register("Any", [], [])` (`parser.spl:1316`) in a file that declares a struct `Any`
     with fields.
   All other register calls there are guarded by `named_type_find(...) < 0` or register a field-less
   generic-instance key (`named_generic_instance_register`, `types.spl:1569-1580`), where the guard does not
   fire.
4. **Harmless today.** The bridge turns named tags into `TypeKind.Named(type_tag_name(tag), args)`
   (`convert_nodes.spl:571-581`), i.e. by NAME, so the duplicate row produces the same AST. The registry is
   then wiped by the next file's `reset_all_pools`. No consumer outside `10.frontend/core/` calls
   `named_type_find`/`named_type_register` (only the legacy C codegen and core interpreter, which do not take
   the flat-AST cache). Not the cause of the Stage 3 items.spl AV (see that record).

Residual risk: any future consumer that resolves by id rather than name, or a path that append-parses
(`parse_module_file`, `parser.spl:1529`, no reset) on top of restored pools, would expose the empty ownership.

## Repro sketch (for the duplicate-row divergence)
1. `reset_all_pools()`; `named_type_set_current_module("p")`;
   `val id = named_type_register("Foo", ["x"], [TYPE_I64])`.
2. `val blob = flat_pools_dump_all()`; `reset_all_pools()`; `named_type_set_current_module("p")`;
   `flat_pools_restore_all(blob)`.
3. `named_type_register("Foo", ["x"], [TYPE_I64])` returns `id + k` (a new row), not `id`.
   On the miss path (skip step 2) it returns `id`.

## Proposed fix (when a consumer needs it)
Prefer **rebuilding on restore** over encoding: after the length/owner validation in
`flat_type_pools_restore` (after `types.spl:2255`, not at `:2211`), set `named_type_modules[i] =
named_type_current_module` for owner rows (`named_type_layout_owners[i] == i`, every row created by
`named_type_register`) and `""` for `named_type_apply` rows, matching what a fresh parse produces. This is
path-independent (blobs can come from a shared store, `module_assembly.spl:1753-1755`, so an encoded
absolute path could mismatch), needs no `FLAT_POOL_CODEC_VERSION` bump and leaves the packed `.spab` path
untouched. Then add `named_type_modules` to the codec-complete guard's documented exclusions with that
reason. The alternative, encoding the list (`flat_pool_enc_text`) at the same position in dump and restore
plus a `FLAT_POOL_CODEC_VERSION` bump (`core/flat_pool_codec.spl:77`), invalidates every cache entry and
still leaves 4 other offenders in the guard.

## Decision
Implemented the "rebuilding on restore" fix (2026-11-25):

1. `src/compiler/10.frontend/core/types.spl` (`flat_type_pools_restore`): after all length,
   `named_generic_instance_*`, `named_type_layout_owners`, and `named_type_argument_graph_valid`
   validation checks pass, `named_type_modules` is rebuilt to `named_type_names.len()` with
   `named_type_current_module` for owner rows (`named_type_layout_owners[i] == i`) and `""` for
   `named_type_apply` instance rows. Rejected restores leave `named_type_modules` empty (`[]`).
2. `scripts/check/check-flat-ast-codec-complete.shs`: added `named_type_modules` to `EXCLUDE_RE`
   with inline rationale explaining the transient rebuild instead of serializing paths.
3. `test/01_unit/compiler/frontend/flat_type_pools_named_type_modules_restore_spec.spl`: targeted
   unit spec covering owner vs `named_type_apply` rows, trailing `named_type_apply`, empty
   `named_type_current_module`, idempotent `named_type_register` + cross-module isolation after
   restore, `build_module_from_flat_pool_blob` cache hits, and failed restores.
