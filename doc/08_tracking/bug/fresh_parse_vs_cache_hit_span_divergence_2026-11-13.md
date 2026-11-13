# Fresh parse and front-end cache hit lower to different HIR (span offsets) (2026-11-13) — FIXED

**Binary:** `/home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple` (Rust seed,
119570696 bytes, 2026-11-05 18:12), worktree `simple-nodestore-20261113` on
`work/node-storage-phase-c-20261113` (base `bd42e7997a4`), `simple test` lane.

**Symptom.** For one parse of `src/compiler/20.hir/hir_lowering/attr_access_sites.spl`, the
boxed `ParserModule` returned by `parse_and_build_module_scoped` and the one rebuilt from the
captured pool blob of the SAME parse (`build_module_from_flat_pool_blob`, the `.fpc` line
cache hit) lower to HIR codec blobs (`hir_module_encode`) of equal length (25,718 lines) that
differ in **2,706 lines**. The packed `.spab` restore (`build_module_from_packed_view_v1`) is
byte-identical to the line-cache restore (0 differing lines), so both production cache-hit
formats agree with each other and disagree with the fresh parse. `src/lib/common/text_bytes.spl`
shows no difference.

**Shape.** The differing scalars are span fields. First difference (codec line 6347): the
empty dict literal `{}` at line 152 col 43 (`var tree_of_class: Dict<text, text> = {}`) has
`start=11 end=11 ... len=0` from the fresh parse and `start=6960 end=6962 ... len=2` from the
cache hit. Line/col agree; the cache hit's byte offsets are the consistent ones, so the fresh
in-process bridge reads stale or placeholder offsets for some expression nodes that the dumped
pools carry correctly.

**Impact.** A warm build (cache hit, the default since 2026-10-25) and a cold build of the same
source produce different HIR spans: diagnostics positions and any span-keyed cache identity can
differ between cold and warm builds. Not caused by the node-storage lane (reproduces with only
`flat_ast_bridge` entrypoints), but it fixes the equality oracle of
`test/02_integration/compiler/data/ast_pool_snapshot_spec.spl`: the snapshot is compared to the
cache-hit restore, not to the fresh boxed tree.

**Repro.** In a spec: `flat_pool_capture_arm(); fresh = parse_and_build_module_scoped(src, path,
false); lines = flat_pool_capture_take(); hit = build_module_from_flat_pool_blob(lines, src,
path).unwrap()`, then compare `hir_module_encode(HirLowering.with_filename(path).lower_module(x))`
for `fresh` and `hit` line by line.

## Cause (root-caused in review of PR #8868)

Three locations:

1. `src/compiler/10.frontend/core/string_interpolation_expand.spl`, `parse_interpolation_fragment`:
   `lex_init_with_path(inner.trim(), "")` re-initialises the global lexer on each `{...}`
   fragment and never gave the module's lexer back.
2. `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` (~1800, fresh path): the bridge
   runs after the interpolation post-pass, so it converts every expression span
   (`convert_nodes.spl` `convert_span`) while the lexer still holds the LAST fragment.
3. `src/compiler/10.frontend/core/lexer.spl` `lex_source_byte_offset`: clamps every char offset to
   the live source's length, so every later offset became the fragment length
   (`f.symbol.id` = 11 in `attr_access_sites.spl`, hence `start=11`).

A cache hit calls `parser_init_with_path(source, path)` before restoring the pools, so its lexer
is the module and its offsets were right. The bridge's generic type-bound sub-parse
(`convert_nodes.spl` `convert_decl_function_type_params`) had the same shape mid-bridge and is
fixed the same way.

## Fix (`e333c37af8f`, branch `work/interp-lexer-span-fix-20261113`)

- Both sub-parses lend the module lexer out with `lexer_state_take()` and take it back with
  `lexer_state_install(...)` (owner move of the lexer's slot arrays; no copy, no lock, no
  `nil`/`any`). The env mirrors (`SIMPLE_BOOTSTRAP_LEX_SOURCE/PATH`) are not restored: they are
  read only when the inline source slot is empty, and install restores it non-empty.
- With real offsets, the char->byte cursor in `lex_source_byte_offset` rewound to 0 on every
  backward query (the bridge converts out of source order): O(n) per span on non-ASCII sources
  (`data_schema_resolver.spl` parse 9.7 s -> 102 s). It is replaced by a per-source prefix table
  built once (`lex_span_byte_prefix`). This was also the cause of
  `flat_pool_restore_10x_slower_than_parse_interpreter_2026-11-13.md` (cache hits always had the
  real lexer).

Evidence (seed binary `.../bootstrap.generations/8ea37491...e467bc/simple`, 119,570,696 bytes):
`test/01_unit/compiler/frontend/interp_lexer_span_restore_spec.spl` RED 0/2 (got 4 and 10, the
fragment lengths) -> 2/2; `interp_fragment_span_spec` was red on base with the same clamp (11 vs
126) -> 3/3 after its warm module covers the probed offset; fresh HIR == cache-hit HIR on
`attr_access_sites`, `text_bytes`, `data_schema_resolver`; `ast_pool_snapshot_spec` 5/5 with the
fresh parse as oracle. Parse time, 3 reps each: `attr_access_sites` 2.03-2.05 s -> 2.09-2.10 s
(ASCII, take/install only), `data_schema_resolver` 9.65-9.86 s -> 6.21-6.35 s.
`interp_fragment_sticky_error_spec` "keeps brace-literal function scopes isolated" fails before
and after (unrelated, pre-existing).

## Blast radius

Every cache-MISS parse of a module containing string interpolation (or a generic type bound),
since the fragment sub-parse was introduced: wrong expression byte offsets (start/end/length;
line:col were right) for every expression converted after the last fragment, i.e. LSP ranges,
span-keyed cache identity, offset-based source slicing and diagnostics byte ranges; cold and warm
builds produced different HIR for the same source. Cache hits were correct.

## Follow-ups (review of PR #8879, branch `work/lexer-span-followups-20261113`)

All test-first in `test/01_unit/compiler/frontend/interp_lexer_span_restore_spec.spl` (RED 2/5 ->
GREEN 5/5, non-ASCII sources, no padding):

1. **Release kept the span table.** `lexer_release_parse_source_globals` now also clears
   `lex_span_byte_prefix` and `lex_span_all_ascii` (RED: 54 entries left after release). On
   `data_schema_resolver.spl` the released table held 26,284 entries; process RSS read the same
   before and after release (509,710,336 B both; the interpreter heap does not return pages), so
   the gain is reachability, not an RSS drop on this lane.
2. **Bridge fragment base converted twice.** `flat_bridge_build_string_regions` fed a BYTE base
   (`span.start + 1 + i + 1`) into the span pool, whose offsets `flat_expr_span` converts char ->
   byte, so non-ASCII modules overshot (RED: 78 vs 75; before #8879 it clamped instead). The base
   is now converted back with the new `lex_source_char_offset` (binary search over the same
   prefix table; identity on ASCII sources).
3. **Module-parse fragments were never rebased.** `parse_string_interpolation_regions` called
   `parse_interpolation_fragment` without a base, so a fragment's own span was `start=0, line 1,
   col 1` (RED: 0 vs 72). It now takes the literal's span id from both module-parse callers and
   rebases through `parse_interpolation_fragment_at`. Reviewer probe: `start=107/139, line 3,
   col 25` for the ASCII/UTF-8 cases (want 107/139).
4. `lexer_byte_spans_spec` dedent case compares against `source.byte_len()`.

Known approximation kept from the bridge path: a region base counts bytes of the DECODED literal
value, so an escape before the `{` (e.g. `\n`) shifts the base by the escape's width.
Parse time, interleaved base/fix runs (3 reps each, same seed binary): `attr_access_sites`
2.09-2.12 s vs 2.07-2.13 s, `data_schema_resolver` 6.14-6.47 s vs 6.25-6.42 s (no change).
`ast_pool_snapshot_spec` 5/5; `lexer_snapshot_spec` (import `core.ast` unresolved) and one
`persistent_parse_owner_contract_spec` example fail identically on the base (pre-existing).
