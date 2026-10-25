# ParseContext: frontend module-var inventory

Companion to `parse_context_per_context_state.md`. Census of every
module-scope `var` under `src/compiler/10.frontend` (761 at
`origin/release/1.0.0`, 2026-10-25), classified by name, initializer and
owning file, then reviewed per file. Re-run the census with
`grep -rnE '^(pub )?var ' src/compiler/10.frontend --include=*.spl`.

| bucket | count | meaning |
|--------|------:|---------|
| A. covered | 273 lines in 9 owner files | in a stage-1 snapshot, or deliberately process-wide in those files (caches, latches, arena generation) |
| D. off parse path | 350 | interpreter, MIR/HIR, type inference/erasure, codegen helpers, test harnesses, coverage inventory, aspect/AOP logging, call graph |
| P. on or near parse path | 138 | classified below |

## P1. Per-parse, needs an owner snapshot next

Reset per file today (or should be). Each gets a `<Owner>State` take/install
like stage 1 and joins `ParseContext`.

| file | vars |
|------|------|
| `core/parser_decls_use.spl` | `par_impl_target_*` (4) |
| `core/parser_expr.spl` | `g_expr_nest_depth` |
| `core/parser_preprocessor.spl` | `_pp_tokens`, `_pp_pos`, `_pp_target_*` (5) |
| `core/representation_declarations_v1.spl` | `representation_*_v1` (9) |
| `core/_ParserDecls/extend_decls.spl` | `EXTEND_*` (7) |
| `core/parser_decls_fn.spl`, `core/_ParserDecls/fn_struct_decls.spl` | `file_generic_constraints`, `file_generic_constraint_modes` (duplicated name in two files) |
| `core/lexer_struct.spl` | `core_last_token_*_slot` (4), `core_token_text_intern` |
| `core/flat_pool_codec.spl` | `_flat_pool_sanitize_capture`, `_flat_pool_capture_poisoned`, `_flat_pool_type_trace*`, `_flat_pool_validate_only` |
| `desugar/placeholder_lambda.spl` | `_ph_*` (7) |
| `_FlatAstBridge/convert_nodes.spl` | `g_pending_defers` |
| `core/collection_feedback.spl` | `_parser_collection_*` (3) |
| `core/capture_write_check.spl` | `cw_*` (9) |
| `core/closure_analysis.spl` | `closure_warnings`, `closure_scope_depth`, `scope_vars`, `var_depth_map` |
| `effect_registry.spl`, `layer_eq_registry.spl` | the `*_pending_*` fields only |

## P2. Cross-file registries (shared by design)

`effect_registry_*`, `layer_eq_registry_*`, `resource_registry_*`,
`rt_criticality_*`, `_facet_static_routes`. They accumulate across every
parsed module, so they are not per-parse. For fibers they stay shared. For
threads (stage 4) they need a lock or a per-worker merge.

## P3. Process-wide, stays global

Caches, memos, stats counters and trace switches: `frontend_parse_cache.spl`
(scope memo, hit/miss/store), `frontend_shared_parse_cas_v1.spl` authority
state, `_cfg_host_arch_cache`, `si_stat_*`, `_collection_desugar_rewrites`,
`trace_policy.spl` slots, `_frontend_phase_trace_state`,
`_frontend_advisory_slot_v1`, `lexical_scan_*_slot`, `DANGEROUS_KEYWORDS`,
plus every `*_cached`, `*_noted`, `*_prof*`, `*_reported` latch. Counters need
atomics or a per-worker sum before stage 4.

## P4. Off parse path despite location

`core/alloc_inference.spl`, `core/call_edge_utils.spl`,
`core/type_checker.spl`, `core/type_subst.spl`, `core/monomorphize.spl`,
`core/test_lang_basics.spl`: analysis passes or fixtures, not run by the parse
entry. Out of scope for `ParseContext`.

## Order

P1 owners, one small PR each, in the order listed (parser-local first). Then
stage 2 accessors, starting with the `pub var` pools read across files
(`types.spl`, `decl_nodes.spl`, `_AstExpr/nodes.spl`, `ast_stmt.spl`,
`parser.spl` `par_errors`/`par_struct_names`/`par_fixed_array_*`).
