# Private-import visibility sweep (2026-11-13)

- **Ids:** `private_import_visibility_sweep_backend_gpu_2026-11-13` (P3, fixed),
  `private_import_visibility_remainder_1312_pairs_2026-11-13` (P3, open; the id
  keeps the wave-1 figure, the live count is in "Wave 2" below),
  closes `hip_backend_contract_spec_private_hip_backend_fns_2026-11-13`.
- **Branch:** `work/private-import-visibility-sweep-20261113` on `release/1.0.0` (base `33755dd5270`);
  wave 2: `work/private-import-wave2-20261113` (base `3538a1adca8`).
- **Model:** Opus (Fable unavailable).

## Class

`6e4e4da3fb2` / `6d15331f91e` (Nov 7-9) made the seed reject a braced
`use m.{name}` that names a private top-level `fn` of `m` from a file in a
different directory. Specs usually surface it only as `function X not found`;
the real text is in the `[engine-demotion]` / JIT-fallback line:

```
private fn `NAME` of module `MOD` (PATH) is not visible to IMPORTER; mark it `pub` or `export` it
```

Earlier instances: #8930 (`gpu_portable_compute.spl`, 23 fns), #8947
(`gpu_generated_2d_contract.spl`, 6 fns).

## Exact seed rule (src/compiler_rust/compiler/src/interpreter_module/module_loader.rs)

Rule 1 - `check_private_use_names` (:614, called from both the fresh-load and
the cache-hit path, :1125 and :1517):
- only braced group imports (`use m.{a, b as c}`), `export use m.{...}` included;
- `name` is a top-level `Node::Function` with `Visibility::Private` that no
  `export` statement of `m` re-exposes (`private_top_level_fn_names`);
- **same-directory exception:** importer and module in the same (canonical) directory pass;
- pairs listed in `scripts/check/private_import_baseline.txt` (`<repo-rel path>|<name>`) only warn;
- **no test exemption** - `test/**` importers are rejected like `src/**`.
  *(Superseded 2026-11-13, see "Test importers exempt" below.)*

Rule 2 - `check_private_call_visibility` (:2818): a call that reaches a private
fn of another directory's module without a braced import (glob import, or no
import) is rejected; `test/**` callers are exempt; same baseline.

## Test importers exempt (owner decision 2026-11-13, `test_private_import_access_2026-11-13`, fixed)

Owner decision: "test is special, can access" - tests may import private items.
Branch `work/test-private-import-access-20261113` on `release/1.0.0` (base
`517f20ae777`). Model: Opus (Fable unavailable).

- **Seed:** `check_private_use_names` returns early when
  `is_test_caller(importer)` - the exact predicate rule 2 already used (path
  starts with `test/` or contains `/test/`, after `\`->`/` and leading `./`
  stripped). Rules 1 and 2 now agree. **Open owner question (review P1):**
  the shared predicate also exempts ~325 tracked product `.spl` files with a
  `/test/` component (102 in `src/app/test/`, `src/**/debug/formats/test/`,
  `src/compiler/70.backend/linker/test/`, `src/os/kernel/fs/test/`,
  `examples/**/test/`), and - since the seed passes absolute paths - every
  file of a checkout located under a `/test/` directory. Kept as-is because
  the brief required the exact rule-2 definition; narrowing both rules to a
  repo-relative `test/` prefix is the follow-up.
- **Self-hosted:** `private_fn_import_denied` (HIR,
  `module_import_resolution.spl`) returns early on
  `private_import_is_test_importer`, a line-for-line mirror of `is_test_caller`.
- Only the importer side is exempt; no fn was made `pub`; product importers
  (`src/`, `scripts/`, `examples/` outside a `/test/` component, a `contest/`
  dir, and a `src/` importer of a private fn defined under `test/`) are still
  rejected. The seed fixtures live under `get_temp_dir()`; a `TMPDIR` with a
  `/test/` component would exempt the negative examples.
- Of the 2,697 remaining rule-1 rows above, the 1,924 with a `test/**`
  importer stop failing.

**Red -> green** (seed built from this tree, `before` = base `a2156a1f`,
`after` = fix `ee15b57c` (sha256 prefixes), `systemd-run MemoryMax=16G timeout 900`, serial;
no `src/` change other than the two checks):

| spec | before | after |
|---|---|---|
| test/01_unit/lib/common/mock_spec.spl | 0/1 (load fail) | **41/41** |
| test/01_unit/compiler/blocks/typed_parser_highlighting_spec.spl | 0/1 | **12/12** |
| test/01_unit/compiler/mir/same_named_struct_layouts_across_modules_spec.spl | 0/1 | **4/4** |
| test/01_unit/compiler/loader/resource_lifecycle_cardinality_spec.spl | 0/1 | **2/2** |
| test/01_unit/app/buildrunner/remote_container_authority_v2_spec.spl | 0/1 | **10/10** |
| test/01_unit/app/buildrunner/remote_parent_integration_v1_spec.spl | 0/1 | **5/5** |
| test/01_unit/spec/dsl_spec.spl | 0/1 | 11/14 (rest: other class) |
| test/01_unit/app/tooling/base64_utils_spec.spl | 0/1 | 34/38 (rest: other class) |

Every "before" log has `is not visible to .../test/...`; no "after" log does.
Specs such as yoga_layout/color_diff/termio_parser/devhub_* were already green
"before" only through the JIT -> interpreter fallback; after, the JIT no longer
demotes on them.

New specs: `private_fn_import_visibility_prevention_spec.spl` (test importer
loads; `contest/` and `app/` importers still get the diagnostic) and
`private_fn_import_cross_module_visibility_spec.spl` (HIR, strict mode:
`test/...` and `/repo/test/...` importers silent, `src/contest/...` still
`E-HIR-PRIVATE-IMPORT-001`) - 8/11 -> 9/11 (the test-importer example
red -> green) and 8/10 -> 10/10 (12/12 after the review added `./`, backslash and test-defined-provider probes). Rust unit test
`test_importer_is_exempt_but_src_importer_still_errors` fails without the
early return and passes with it. Neighbouring loader specs unchanged:
`private_fn_call_visibility_spec` 3/3, `module_qualified_type_registry_spec`
8/8 before and after.

**Pre-existing reds, not caused here:** `private_fn_import_visibility_spec`
(0/1) and the prevention spec's "missing from the baseline errors" / "nested
baseline copy" examples fail identically before and after: the JIT reports the
`is not visible` error, then the JIT -> interpreter fallback runs the program
anyway with rc 0, so `rc != 0` assertions fail. The new negative examples
assert the diagnostic text instead of rc for that reason.

**Baseline:** rows are `definer|name` with no importer column, and
`check-private-import-baseline.shs` calls a row stale only when the file is gone
or the fn is no longer private - so the exemption makes nothing stale by the
gate's definition (`--prune` would remove nothing). Rows needed only by tests
were pruned by hand: a row was removed when (a) the Appendix A scan with the
baseline filter off finds at least one importer and every importer is a test
file, and (b) no non-test tracked `.spl` outside the definer's directory
mentions the name as a token at all (covers rule-2 glob calls and scan misses).
Rows whose definer is in `src/compiler/10.frontend` or `60.mir_opt` (127) were
kept for the parallel w2 `pub` lane. **8,044 of 19,642 rows removed (11,598
left)**; `check-private-import-baseline.shs --base origin/release/1.0.0`:
`PASS - 11598 baseline entries checked, 0 stale, 0 added`.

## Census (static, awk/sh - scripts in the appendix)

Rule 1 resolver: module path -> file by longest trailing segment match
(`NN.` layer prefixes stripped), `x.spl` preferred over `x/mod.spl` /
`x/__init__.spl`. Validation:

- **Recall vs the independent baseline:** with the baseline filter disabled the
  scan reproduces 18,774 of the 19,597 `src|test|scripts` baseline pairs (95.8%).
- **Oracle:** 9 of 9 sampled specs agree with the seed (6 flagged and red with
  the exact "is not visible" text naming the same module path; 3 initially
  flagged by a looser suffix resolver were green and are no longer flagged).

| Rule 1 census | rows (importer, module, fn) | (module, fn) pairs | modules |
|---|---|---|---|
| before this change | 3,303 | 1,710 | 402 |
| fixed here (`src/compiler/70.backend/**` + `src/lib/**/{gpu*,cuda,render}/`) | 606 | **398** | 63 |
| remaining (open P3) | 2,697 | 1,312 | 339 |

Remaining rows: 1,924 have a `test/**` importer, 61 are `export use` re-exports.

**Count note (re-measured in wave 2).** Figures of 1,712 before / 1,314
remaining have been quoted for this sweep; they are not reproducible. Re-running
Appendix A on the wave-1 base `33755dd5270` gives exactly 3,303 rows / **1,710**
pairs, so 1,710 - 398 = **1,312** remaining, matching the table and the bug id.
On the wave-2 base `3538a1adca8` the same scan gives 2,698 rows / **1,313**
pairs; the one new pair is `src/compiler/90.tools/fix/rules/impl_/lint_code.spl`
`check_non_exhaustive_match_with_lines`, imported by
`test/01_unit/compiler/lint/non_exhaustive_match_catch_all_spec.spl`, which
landed between the two bases.

Known census limits (independent review): where a `std.X` path names no
variant, every equally-matching variant file is counted although the seed
loads one (possible over-count); the scan prefers `x.spl` over `x/__init__.spl`
while one seed lookup path checks `__init__.spl` first; `pub use` lines are not
parsed. 30 of the 398 fixed fns (`src/lib/gc_async_mut/gpu/engine2d/{color,glyph,helpers_*}.spl`)
are justified only by `export use std.nogc_async_mut.gpu.engine2d.<x>.{...}`
re-exports that the scan resolves across variants; if the seed does not fall
back across variants there, those 30 `pub`s are unneeded but harmless. The
other 368 have a braced cross-directory importer.

Rule 2 (glob-import calls from `src/` + `scripts/` callers, last-two-segment
resolution, **not oracle-validated**): ~527 rows / 361 (module, fn) pairs.
This sweep did not change rule-2 sites; it is recorded as a known gap.

## Fix

`pub` added to exactly the 398 flagged fns (63 files); the diff is 398
one-line `fn` -> `pub fn` changes, nothing else. No spec, assertion, or
baseline entry changed (no fixed fn was baselined, so the baseline gate's
stale check is unaffected).

Clash check: the only glob importers of the touched modules that mention a
fixed name (`encode_riscv_spec`, `allow_suppressions_spec` x2) only *call* it;
none defines or imports it elsewhere. Only `cuda_get_device_name` and
`cuda_stream_create` now have more than one `pub` definition, with identical
signatures across `nogc_sync_mut`/`nogc_async_mut` (no
`co-compiled definitions with differing signatures` warning). The
collision-warning set in every verification log is identical before/after.

## Red -> green (seed `seed-whileval`, `systemd-run MemoryMax=16G timeout 900`, serial)

| spec | before | after |
|---|---|---|
| test/01_unit/compiler/codegen/hip_backend_contract_spec.spl | 0/5 | **5/5** |
| test/01_unit/compiler/backend/cranelift_gemm_fusion_spec.spl | 0/3 | **3/3** |
| test/01_unit/compiler/backend/native/isel_x86_64_spec.spl | 1/6 | **6/6** |
| test/01_unit/compiler/backend/llvm_tool_resolution_spec.spl | 1/2 | **2/2** |
| test/01_unit/compiler/backend/backend_basic_spec.spl | 0/3 | **3/3** |
| test/01_unit/compiler/backend/native/x86_avx512_owner_routing_spec.spl | 1/4 | **4/4** |
| test/01_unit/compiler/backend/cranelift_module_static_contract_spec.spl | 0/4 | **4/4** |
| test/01_unit/compiler/backend/llvm_host_toolchain_spec.spl | 0/6 | **6/6** |
| test/01_unit/compiler/codegen/opencl_backend_contract_spec.spl | 0/19 | 14/19 |

Every "before" log carries the "is not visible" text; no "after" log does.
The hip spec's second symptom (`emit_portable_2d_fill_u32_kernel not found`,
reported at `gpu_portable_compute.spl:940` but attributed to the spec) cleared
with the same fix. opencl's 5 remaining reds are a different class
(`PLUG-E-NOTFOUND: backend=opencl`). Control: three specs the loose resolver
had flagged (`cuda_session_contract_spec` 10/10, `graph_ir3d_spec` 6/6,
`engine2d_readback_metadata_spec` 2/2) are green before and after.

## Wave 2 - `src/compiler/10.frontend` + `src/compiler/60.mir_opt` (base `3538a1adca8`)

Scope rule (owner, 2026-11-13): **tests may access private fns**; the seed's
`check_private_use_names` test exemption lands in a separate lane. So only a
pair with at least one non-test importer (outside `test/**` and not a
`*_spec.spl`) is made `pub`; test-only pairs stay private.

| census at `3538a1adca8` | pairs | non-test | test-only |
|---|---|---|---|
| whole tree, before wave 2 | 1,313 | 496 | 817 |
| `10.frontend` + `60.mir_opt` | 354 (231 + 123) | 166 (119 + 47) | 188 |
| made `pub` here | **165** (118 + 47), 33 files | 165 | 0 |
| whole tree, after wave 2 | **1,148** (324 modules, 2,240 rows) | **331** | **817** |

The one non-test pair left private is `core/parser.spl` `parser_warn`:
`test/01_unit/compiler/frontend/parser_guarded_int_single_scan_spec.spl`
slices `parser.spl` source between `fn parser_guarded_int_text(` and the literal
`"\nfn parser_warn(msg: text):"`, so `pub` turns it 7/7 -> 6/7 (measured).
Changing the spec anchor was out of scope for this wave; its four importers
(`_ParserDecls/enum_module_body.spl`, `_ParserPrimary/{asm_match_suffix,asm_raw_parsing,primary_expr}.spl`)
are unchanged from the base.

Checks: the diff is 165 one-line `fn` -> `pub fn` changes and nothing else;
`check-private-import-baseline.shs --range 3538a1adca8..<tip>` = PASS, 0 stale,
0 added. Clash check: none of the 165 names has another column-0 `pub`/`export fn`
definition anywhere; the files that define a same-named fn at any visibility
(28 sites, mostly methods: `eval_expr`, `is_alpha`, `int_to_str`, `glob_match`,
`eval_stmt`, `eval_block`; `eval_expr`/`eval_stmt` are also named in `export`
lists of `src/lib/gc_async_mut/pure/evaluator.spl` and
`src/app/interpreter/expr/__init__.spl`) import no changed module; the only glob importers of a
changed module that mention a changed name are `_FlatAstBridge/{convert_nodes,module_assembly}.spl`,
which brace-import the same names from the same module (benign).
Seed `compile` of every touched file: no `parse:` error in any touched file
(the three `parse:` failures are `simd_recipe_infra.spl:91`, an untouched
dependency, identical on the base).

New census gap found by the seed oracle: a braced import through an
`export use m.*` facade is not followed by the rule-1 scan.
`interpreter/eval_calls.spl` imports `eval_struct_constructor` and
`eval_enum_variant_call` from `interpreter.eval_ops`, which re-exports
`_EvalOps/call_method_eval.*` and `_EvalOps/access_literal_assign_eval.*`,
where both are private; the seed rejects the first (`is not visible to ...eval_calls.spl`),
which is the remaining red in `module_namespace_alias_runtime_spec`,
`static_class_method_dispatch_spec` and `core_interpret_mut_struct_param_alias_spec`. Not fixed here (outside the census list).

Red -> green (seed `seed-whileval`, `systemd-run MemoryMax=16G timeout 900`,
serial; "before" = the 33 files restored to `3538a1adca8`, "nv" = count of
`is not visible` lines):

| spec | before | after |
|---|---|---|
| test/01_unit/compiler/interpreter/todo_builtin_spec.spl | ERROR 0/0, nv 3 | **1/1**, nv 0 |
| test/01_unit/compiler/backend/crc32_idiom_semantics_spec.spl | 2/5, nv 2 | **5/5**, nv 0 |
| test/01_unit/compiler_core/interpreter/range_for_no_silent_iteration_cap_spec.spl | ERROR 0/0, nv 3 | **4/4**, nv 0 |
| test/01_unit/compiler_core/interpreter/range_overflow_degenerate_spec.spl | ERROR 0/0, nv 3 | **4/4**, nv 0 |
| test/01_unit/compiler/interpreter/enum_instance_method_dispatch_spec.spl | 0/3, nv 3 | **3/3**, nv 0 |
| test/01_unit/compiler/interpreter/enum_qualified_payload_pattern_spec.spl | 2/6, nv 4 | **6/6**, nv 0 |
| test/01_unit/compiler/interpreter/module_namespace_alias_runtime_spec.spl | 1/10, nv 9 | 8/10, nv 2 (facade gap above) |
| test/01_unit/compiler/interpreter/static_class_method_dispatch_spec.spl | 1/3, nv 2 | 2/3, nv 1 (facade gap above) |
| test/01_unit/compiler/mir_opt/ssa_alloca_ret_operand_unwrap_free_spec.spl | 2/3, nv 2 | 2/3, nv 0 (other failure) |
| test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl | 4/6, nv 2 | 4/6, nv 0 (other failure) |
| test/01_unit/compiler/mir_opt/var_reassign_terminator_option_slots_spec.spl | 6/6 via JIT demotion, nv 2 | 6/6, nv 0 |
| test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl | 4/4 via JIT demotion, nv 2 | 4/4, nv 0 |
| test/01_unit/compiler_core/interpreter/stmt_for_comprehension_no_silent_iteration_cap_spec.spl | ERROR 0/0, nv 3 | no verdict: killed at the 900 s cap twice, nv 0 (the import now resolves; the spec body is slow or hangs - not investigated here) |

The six bold rows were re-run on the final tree (with `parser_warn` private)
and are unchanged; `parser_union_decl_owner_spec` 3/3 there too. Of the other
31 screened specs (all flagged imports in this wave), 21 were green before and
after (incl. `parser_guarded_int_single_scan_spec` 7/7 once `parser_warn` stayed
private), 9 were red before and after with no `is not visible` line in either
(unrelated failures, identical counts), and
`core_interpret_mut_struct_param_alias_spec` stays 0/6 on the facade gap
(`eval_struct_constructor`, nv 6 before and after).
No "after" log carries an `is not visible` line naming a wave-2 module except
the facade `_EvalOps/call_method_eval.spl` one.

## Remaining (open P3) - per module (after wave 2, base `3538a1adca8`)

1,148 pairs in 324 modules. `non-test` = pairs with at least one importer outside
`test/**` that is not a `*_spec.spl`; the other 817 are test-only (see Wave 2).

| module | fns | non-test | names |
|---|---|---|---|
| `src/lib/common/yaml/utilities.spl` | 40 | 0 | yaml_compact_print, yaml_count_nodes, yaml_deep_copy, yaml_depth, yaml_detect_indentation, yaml_equals, yaml_escape_string, yaml_flatten_mapping, yaml_from_string, yaml_get_nested, yaml_indent, yaml_is_empty, yaml_mapping_contains_value, yaml_mapping_exclude_keys, yaml_mapping_filter_keys, yaml_mapping_get, yaml_mapping_has, yaml_mapping_keys, yaml_mapping_remove, yaml_mapping_set, yaml_mapping_size, yaml_mapping_values, yaml_merge_mappings, yaml_pretty_print, yaml_quote_string, yaml_sequence_append, yaml_sequence_contains, yaml_sequence_get, yaml_sequence_index_of, yaml_sequence_insert, yaml_sequence_length, yaml_sequence_remove, yaml_sequence_reverse, yaml_sequence_set, yaml_sequence_slice, yaml_set_nested, yaml_to_string, yaml_unescape_string, yaml_validate_indentation, yaml_validate_schema |
| `src/app/llm_caret/claude_full/native_ts/yoga_layout/index.spl` | 26 | 0 | autoValue, boundAxis, calculateBaseline, collectLayoutChildren, computeFlexBasis, crossAxis, defaultEdges, hasAnyAutoEdge, hasAnyDefinedEdge, hasMeasureFuncInSubtree, isReverse, isRow, layoutNode, leadingEdge, loadYoga, parseDimension, percentValue, physicalEdge, pointValue, resolveChildAlign, resolveEdge, resolveFlexibleLengths, resolveGap, resolveValue, trailingEdge, undefinedValue |
| `src/app/llm_caret/claude_full/native_ts/color_diff/index.spl` | 26 | 0 | ansi256FromRgb, ansiIdx, applyBackground, asTerminalEscaped, charWidth, colorToEscape, decorationColor, defaultSyntaxThemeName, detectColorMode, detectLanguage, dimContent, findAdjacentPairs, flattenHljs, getNativeModule, getSyntaxTheme, highlightLine, leftPad, lineBackground, maxLineNumber, parseMarker, rgb, splitLinesDropTrailing, tokenize, wordBackground, wordDiffStrings, wrapText |
| `src/compiler_rust/lib/std/src/tooling/algorithm_utils.spl` | 24 | 0 | binary_search, bubble_sort, count_occurrences, drop, find_all_indices, find_max, find_max_index, find_min, find_min_index, find_sublist, insertion_sort, is_prefix, is_sorted, is_suffix, linear_search, lists_equal, merge_sort, merge_sorted, quick_sort, remove_duplicates, reverse_list, selection_sort, sum, take |
| `src/compiler/10.frontend/core/interpreter/value.spl` | 23 | 0 | val_array_at, val_array_clear, val_array_copy, val_array_cow_copy_count, val_array_len, val_array_pop, val_array_push, val_array_set, val_get_bool, val_init_cache, val_is_int, val_is_nil, val_is_text, val_make_array, val_make_float, val_make_nil, val_make_struct, val_make_text, val_reset, val_struct_get_field, val_struct_set_field_idx, val_struct_upsert_field, val_to_text |
| `src/lib/nogc_sync_mut/mcp/jj/tools_git_core.spl` | 18 | 18 | handle_git_add, handle_git_blame, handle_git_clone, handle_git_commit, handle_git_diff, handle_git_init, handle_git_log, handle_git_show, handle_git_status, schema_git_add, schema_git_blame, schema_git_clone, schema_git_commit, schema_git_diff, schema_git_init, schema_git_log, schema_git_show, schema_git_status |
| `src/lib/nogc_async_mut/mcp/jj/tools_git_core.spl` | 18 | 18 | handle_git_add, handle_git_blame, handle_git_clone, handle_git_commit, handle_git_diff, handle_git_init, handle_git_log, handle_git_show, handle_git_status, schema_git_add, schema_git_blame, schema_git_clone, schema_git_commit, schema_git_diff, schema_git_init, schema_git_log, schema_git_show, schema_git_status |
| `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` | 18 | 0 | create_exact_rule_binding, lookup_exact_rule_binding, optimization_fact_list_contains, optimization_rule_provider_builtin_jit_hotspot, optimization_rule_provider_bulk_cmp, optimization_rule_provider_bulk_copy, optimization_rule_provider_bulk_fill, optimization_rule_provider_can_run, optimization_rule_provider_clib_parity, optimization_rule_provider_dynamic, optimization_rule_provider_endian_load, optimization_rule_provider_endian_store, optimization_rule_provider_has_required_fact, optimization_rule_provider_is_runtime_hotspot, optimization_rule_provider_should_embed, optimization_rule_provider_uses_direct_lookup, rule_lookup_stats_record, rule_lookup_stats_zero |
| `src/compiler/10.frontend/core/interpreter/eval_tables.spl` | 18 | 0 | enum_table_lookup_in, enum_table_register, enum_table_register_in, enum_table_remove, enum_table_reset, enum_variant_is_declared, func_table_remove_owned, match_fallthrough_get_abort, match_fallthrough_message, match_fallthrough_set_abort, match_wildcard_catch_get_enabled, match_wildcard_catch_message, match_wildcard_catch_set_enabled, must_use_get_reason, must_use_is_critical, must_use_is_registered, must_use_scan_source, report_match_wildcard_catch |
| `src/compiler_rust/lib/std/src/spec/dsl.spl` | 17 | 0 | after_all, after_each, before_all, before_each, context, context_def, describe, get_let, given, given_lazy, has_let, ignore_it, include_examples, it, it_behaves_like, let_lazy, shared_examples |
| `test/fixtures/global_write_visibility/gwv_owner.spl` | 16 | 0 | gwv_read_at, gwv_read_len, gwv_read_n, gwv_reset, gwv_w_array, gwv_w_array_xmod, gwv_w_indexed, gwv_w_indexed_xmod, gwv_w_midwrite, gwv_w_nested_if, gwv_w_nested_if_xmod, gwv_w_push_loop, gwv_w_push_loop_xmod, gwv_w_scalar, gwv_w_scalar_xmod, gwv_w_then_return_n |
| `src/lib/nogc_sync_mut/mcp/jj/tools_git_misc.spl` | 16 | 16 | handle_git_bisect, handle_git_clean, handle_git_config, handle_git_reset, handle_git_revert, handle_git_set_working_dir, handle_git_stash, handle_git_worktree, schema_git_bisect, schema_git_clean, schema_git_config, schema_git_reset, schema_git_revert, schema_git_set_working_dir, schema_git_stash, schema_git_worktree |
| `src/lib/nogc_async_mut/mcp/jj/tools_git_misc.spl` | 16 | 16 | handle_git_bisect, handle_git_clean, handle_git_config, handle_git_reset, handle_git_revert, handle_git_set_working_dir, handle_git_stash, handle_git_worktree, schema_git_bisect, schema_git_clean, schema_git_config, schema_git_reset, schema_git_revert, schema_git_set_working_dir, schema_git_stash, schema_git_worktree |
| `src/compiler_rust/lib/std/src/spec/mock.spl` | 16 | 4 | arg_any, arg_exact, arg_gt, arg_gte, arg_in_range, arg_lt, arg_lte, matches_arg, mock_policy_disable, mock_policy_init, mock_policy_init_hal_only, mock_policy_init_with_patterns, mock_policy_is_enabled, mock_policy_matches_any_pattern, mock_policy_matches_hal_pattern, mock_policy_reset |
| `test/helpers/simpleos_complete_os_hardening_steps.spl` | 15 | 0 | check_simpleos_capability_matrix, check_simpleos_filesystem_conformance, check_simpleos_filesystem_exec, check_simpleos_perf_duplication, check_simpleos_server_protocols, check_simpleos_toolchain_fs, check_simpleos_wm, simpleos_evidence_owner, step_boot_target, step_compile_and_run_hello, step_exercise_window_manager, step_launch_from_filesystem, step_measure_resource_budget, step_mount_filesystem, step_probe_protocol |
| `test/system/os_tls_hosted_interop_helpers.spl` | 14 | 0 | cleanup_fixture_dir, cleanup_server_processes, ensure_server_bin, file_exists, kill_server, make_temp_fixture_dir, run_openssl_client, run_simple_client, seed_fixture_dir, server_bin, simple_bin, sleep_ms, spawn_server, write_server_config |
| `src/lib/nogc_async_mut/lsp/lsp_json.spl` | 14 | 0 | escape_json, extract_field, extract_id, extract_nested, jo1, jo2, jp, js, LB, make_json_result, Q, RB, SB_L, SB_R |
| `src/lib/gc_async_mut/lsp/lsp_json.spl` | 14 | 0 | escape_json, extract_field, extract_id, extract_nested, jo1, jo2, jp, js, LB, make_json_result, Q, RB, SB_L, SB_R |
| `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` | 14 | 0 | ssa_alloca_rewrite_operand, ssa_alloca_rewrite_term, ssa_collect_inst_operand_locals, ssa_collect_term_operand_locals, ssa_cross_block_live_locals, ssa_local_first_indices, ssa_local_id_value, ssa_local_type_lookup, ssa_max_local_from_inst, ssa_reassigned_param_locals, ssa_replace_operand_local, ssa_rewrite_operand, ssa_term_operand_payloads_valid, _ssa_written_local_id |
| `test/system/qemu/os/common/qemu_os_harness.spl` | 12 | 6 | allocate_live_host_port, can_run_target, _extract_hostfwd_port, _extract_hostfwd_port_from_args, file_exists, read_qemu_stderr_log, read_serial_log, run_os_qemu_with_target_via_timeout, spawn_guest_with_qmp, spawn_guest_with_qmp_scenario, stop_guest, wait_for_serial_marker |
| `test/system/crypto_ref_harness.spl` | 12 | 0 | crypto_input_matrix, ref_aes_128_gcm_decrypt_via, ref_aes_128_gcm_encrypt_via, ref_chacha_poly_decrypt_via, ref_chacha_poly_encrypt_via, ref_ed25519_sign_via, ref_ed25519_verify_via, ref_hmac_sha256_via, ref_sha256_via, ref_sha512_via, ref_x25519_via, vendor_name |
| `src/app/llm_caret/claude_full/ink/termio/parser.spl` | 12 | 0 | cursorStyle, eraseDisplayRegion, eraseLineRegion, findSequenceEnd, graphemeWidth, identifySequence, parseCSI, parseCSIParams, parseOSCSequence, parsePositiveI64, segmentGraphemes, splitCSIParamText |
| `src/lib/nogc_sync_mut/mcp/jj/tools_git_sync.spl` | 10 | 10 | handle_git_fetch, handle_git_pull, handle_git_push, handle_git_remote, handle_git_tag, schema_git_fetch, schema_git_pull, schema_git_push, schema_git_remote, schema_git_tag |
| `src/lib/nogc_sync_mut/mcp/jj/tools_git_branch.spl` | 10 | 10 | handle_git_branch, handle_git_checkout, handle_git_cherry_pick, handle_git_merge, handle_git_rebase, schema_git_branch, schema_git_checkout, schema_git_cherry_pick, schema_git_merge, schema_git_rebase |
| `src/lib/nogc_async_mut/mcp/jj/tools_git_sync.spl` | 10 | 10 | handle_git_fetch, handle_git_pull, handle_git_push, handle_git_remote, handle_git_tag, schema_git_fetch, schema_git_pull, schema_git_push, schema_git_remote, schema_git_tag |
| `src/lib/nogc_async_mut/mcp/jj/tools_git_branch.spl` | 10 | 10 | handle_git_branch, handle_git_checkout, handle_git_cherry_pick, handle_git_merge, handle_git_rebase, schema_git_branch, schema_git_checkout, schema_git_cherry_pick, schema_git_merge, schema_git_rebase |
| `src/compiler/10.frontend/core/interpreter/module_loader_core.spl` | 10 | 0 | import_admission_get_deny, import_admission_set_deny, is_deferred_module, load_module, load_module_selective, module_find_by_file_path, module_get_file_path, module_is_loaded, use_list_warnings_enabled, warn_unprovided_use_names |
| `test/helpers/shared_multilingual_gpu_fonts_perf_evidence.spl` | 9 | 0 | expect_font_perf_budget, font_perf_evidence_record, font_perf_p95, font_perf_rss_growth_percent, font_perf_samples_text, parse_font_perf_evidence, read_font_perf_evidence, unavailable_font_perf_evidence, write_font_perf_evidence |
| `test/02_integration/t32_hw/t32_hw_helpers.spl` | 9 | 0 | t32_hw_backend_preference, t32_hw_connect, t32_hw_ctypes_available, t32_hw_has_software_build, t32_hw_host, t32_hw_port, t32_hw_probe_available, t32_hw_python_available, t32_hw_t32rem_available |
| `src/lib/common/yaml/validate.spl` | 9 | 0 | yaml_create_alias, yaml_create_anchor, yaml_get_alias_name, yaml_get_anchor_name, yaml_get_anchor_value, yaml_is_alias, yaml_is_anchor, yaml_parse_documents, yaml_resolve_aliases |
| `src/lib/common/yaml/serialize.spl` | 9 | 0 | yaml_serialize, yaml_serialize_block, yaml_serialize_documents, yaml_serialize_flow, yaml_serialize_flow_mapping, yaml_serialize_flow_sequence, yaml_serialize_mapping_block, yaml_serialize_scalar, yaml_serialize_sequence_block |
| `src/compiler/99.loader/loader/resource_lifecycle.spl` | 9 | 0 | lifecycleconfig_default, lifecycle_destroy, lifecycle_get_jit_origin, lifecycle_on_jit_triggered, lifecycle_on_module_load, lifecycle_stats, lifecycle_tracked_jit_count, lifecycle_tracked_module_count, lifecycle_with_defaults |
| `test/system/os_crypto_ref_helpers.spl` | 8 | 0 | bytes_to_hex, hex_to_bytes, openssl_ecdsa_p256_verify_der, openssl_hmac_sha256, openssl_major_version, openssl_present, openssl_sha256, openssl_sha512 |
| `src/lib/nogc_async_mut/mcp/resource_utils.spl` | 8 | 8 | current_timestamp, error_json, escape_json, extract_json_array, extract_json_int, extract_json_string, items_to_json, success_json |
| `src/compiler_rust/lib/std/src/tooling/base64_utils.spl` | 8 | 0 | byte_to_char, char_to_byte, decode_base64, decode_base64_url, encode_base64, encode_base64_url, find_base64_index, is_valid_base64 |
| `src/compiler/10.frontend/desugar/spawn_analysis.spl` | 8 | 0 | add_boot_spawn, add_boot_spawn_counts, compute_init_reachable, format_spawn_analysis, format_spawn_verify_result, get_boot_spawn_count, is_in_list, verify_spawn_bounds |
| `test/system/dynload/dynload_fixture_helpers.spl` | 7 | 0 | make_elf64_exec, make_elf64_with_dynsym, make_pe64_export_image, make_pe64_reloc_image, make_smf_wrapped_elf64_exec, push_u32_le, push_u64_le |
| `test/fixtures/bootstrap_builder/phase4_acceptance_helpers.spl` | 7 | 0 | assert_failure_diagnostic, assert_success_output, compile_phase4_fixture, eval_phase4_fixture, phase4_output, require_phase4_binding, run_bound_tool |
| `src/compiler_rust/lib/std/src/tooling/ds_utils.spl` | 7 | 0 | deque_from_list, merge_queues, queue_from_list, queue_get, reverse_stack, stack_from_list, stack_get |
| `src/compiler/99.loader/module_resolver/var_resolution.spl` | 7 | 5 | var_candidate_roots, var_config_selections, var_group_dir, var_module_candidates, var_parse_manifest, var_resolve_selections, var_validate |
| `src/compiler/99.loader/loader/module_loader.spl` | 7 | 0 | lazymoduleloaderconfig_default, lazymoduleloader_new, mangle_name, moduleloader_destroy, moduleloader_load, moduleloader_resolve_symbol, moduleloader_unload |
| `src/compiler/90.tools/duplicate_check/benchmark.spl` | 7 | 7 | compare_benchmarks, format_benchmark_result, format_benchmark_stats, load_benchmark_results, run_benchmark, run_benchmark_iterations, save_benchmark_results |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl` | 7 | 0 | clib_parity_all_rules_are_general, clib_parity_domain_rule_count, clib_parity_rule_by_name, clib_parity_rule_can_rewrite, clib_parity_rule_is_simpleos_safe, clib_parity_rule_provider, clib_parity_rule_rewrite_decision |
| `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` | 7 | 0 | caps_kind_supports_any_pattern_idiom, idiom_for_intrinsic, pattern_idiom_stats_with_remark, pattern_idiom_stats_zero, run_pattern_idiom_pass, run_pattern_idiom_pass_x86, x86_caps_supports_any_pattern_idiom |
| `src/compiler/15.blocks/blocks/testing.spl` | 7 | 0 | assert_parse_fails, assert_parse_succeeds, blockcontext_test, mock_block, test_no_const_eval, test_parse, test_parse_error |
| `src/compiler/15.blocks/blocks/registry.spl` | 7 | 4 | block_registry, get_block, is_block, is_block_registered, register_block, register_builtin_blocks, unregister_block |
| `src/compiler/10.frontend/core/interpreter/ops.spl` | 7 | 0 | ops_clear_error, ops_get_error, val_add, val_div, val_mul, val_negate, val_sub |
| `src/app/io/volatile_ops.spl` | 7 | 7 | volatile_read_u16, volatile_read_u64, volatile_read_u8, volatile_write_u16, volatile_write_u32, volatile_write_u64, volatile_write_u8 |
| `src/app/io/coverage_simple.spl` | 7 | 0 | coverage_clear, coverage_condition, coverage_decision, coverage_enabled, coverage_report, parse_coverage_stats, with_coverage |
| `test/system/reftest/parity/pixel_diff_core.spl` | 6 | 0 | bitmap_diff_rect, max_channel_delta, mismatch_ratio, per_channel_delta, pixel_matches, summarize |
| `test/helpers/hal_coverage_parity.spl` | 6 | 0 | assert_hal_branch_coverage, assert_hal_parity, hal_hash_receipt, prepare_hal_fixture, run_c_hal_case, run_simple_hal_case |
| `test/fixtures/compiler/same_name_layouts/span_b.spl` | 6 | 0 | span_b_copy_len, span_b_eq, span_b_len, span_b_make, span_b_wrap_eq, span_b_wrap_len |
| `test/fixtures/compiler/same_name_layouts/span_a.spl` | 6 | 0 | span_a_copy_end, span_a_end, span_a_eq, span_a_make, span_a_wrap_end, span_a_wrap_eq |
| `src/compiler_rust/lib/std/src/cli_output/_test_len.spl` | 6 | 0 | len_once_i64, len_once_text, len_then_push, len_twice_i64, len_twice_text, push_then_len |
| `test/perf/bench/lib/timing.spl` | 5 | 0 | bench_csv, bench_csv_header, bench_measure, bench_now_ns, bench_print |
| `test/fixtures/storage/dbfs/hosted_fs_no_regression_shared.spl` | 5 | 0 | assert_mount_root_is_dir, assert_mount_root_slash_is_dir, assert_open_returns_handle, assert_readdir_on_root_is_stable, assert_read_returns_empty_or_better |
| `test/fixtures/crypto/x25519mlkem768/canonical_fixture.spl` | 5 | 2 | x25519_mlkem768_fixture_bytes, x25519_mlkem768_fixture_bytes32, x25519_mlkem768_fixture_list, x25519_mlkem768_fixture_list32, x25519_mlkem768_ntt_fixture |
| `src/lib/nogc_sync_mut/lsp/lsp_json.spl` | 5 | 0 | escape_json, extract_id, extract_nested, LB, RB |
| `src/lib/nogc_async_mut/mcp/log_store.spl` | 5 | 5 | format_log_tree_text, log_entries_to_json, log_entry_to_json, log_status_to_json, log_tree_to_json |
| `src/compiler/99.loader/loader/generation_sweeper.spl` | 5 | 0 | sweeper_advance_epoch, sweeper_mark_used, sweeper_new, sweeper_reset, sweeper_tracked_count |
| `src/compiler/90.tools/text_diff.spl` | 5 | 0 | compute_diff, count_additions, count_deletions, count_hunks, format_unified |
| `src/compiler/10.frontend/desugar/reservation_analysis.spl` | 5 | 0 | compute_demand, format_demand, format_reservation_result, get_task_reserve, verify_reservations |
| `src/compiler/10.frontend/core/types.spl` | 5 | 0 | newunit_count, newunit_name_at, newunit_suffix_at, newunit_underlying_tag_at, unit_decl_register |
| `src/compiler/10.frontend/core/interpreter/env.spl` | 5 | 0 | env_assign, env_lookup, env_pop_scope, env_push_scope, env_scope_depth |
| `src/compiler/00.common/dependency/visibility.spl` | 5 | 0 | ancestor_visibility, check_access, dir_effective_visibility, effective_access_policy, visibility_meet |
| `src/app/check/main.spl` | 5 | 0 | checker_begin_file_scope, checker_end_file_scope, checker_scope_owner_poisoned_v1, check_one_full, main |
| `test/fixtures/structural/resolve_golden_v1.spl` | 4 | 0 | resolve_golden_definition_hex, resolve_golden_reference_maxpos_hex, resolve_golden_resolution_resolved_hex, resolve_golden_resolution_zero_hex |
| `test/fixtures/storage/dbfs/posix_baseline.spl` | 4 | 0 | run_posix_append_log, run_posix_metadata_storm, run_posix_mmap_read, run_posix_random_overwrite |
| `test/fixtures/interpreter_receiver_hop_depth/shapes.spl` | 4 | 0 | alias_keeps_snapshot, fill_direct, fill_hops, order_across_hops |
| `src/lib/nogc_sync_mut/ptr/types.spl` | 4 | 4 | ptr_state, ptr_state_expired, ptr_state_moved, ptr_state_valid |
| `src/lib/nogc_sync_mut/mcp/jj/jj_runner.spl` | 4 | 4 | get_default_repo_path, get_jj_version, is_jj_repo, jj_run |
| `src/lib/nogc_sync_mut/daemon_sdk/operation_dispatch_v2.spl` | 4 | 4 | daemon_operation_admit_v2, daemon_operation_begin_v2, daemon_operation_exact_v2, daemon_operation_record_outcome_v2 |
| `src/lib/nogc_async_mut/ptr/types.spl` | 4 | 4 | ptr_state, ptr_state_expired, ptr_state_moved, ptr_state_valid |
| `src/lib/nogc_async_mut/mcp/jj/jj_runner.spl` | 4 | 4 | get_default_repo_path, get_jj_version, is_jj_repo, jj_run |
| `src/lib/gc_async_mut/ptr/types.spl` | 4 | 4 | ptr_state, ptr_state_expired, ptr_state_moved, ptr_state_valid |
| `src/compiler_rust/lib/std/src/spec/registry.spl` | 4 | 1 | get_all_groups, get_context, get_shared_examples, reset_registry |
| `src/compiler_rust/lib/std/src/io/fs.spl` | 4 | 4 | create_dir, create_dir_all, read_text, write_text |
| `src/compiler_rust/lib/std/src/cli_output/_test_multi.spl` | 4 | 0 | test_buffer_len, test_ids_len, test_names_len, test_starts_len |
| `src/compiler/60.mir_opt/mir_opt/storage_access_analysis.spl` | 4 | 0 | analyze_mir_storage_accesses, analyze_mir_storage_access_summary, mir_storage_bindings_well_formed, mir_storage_region_binding_v1 |
| `src/compiler/15.blocks/blocks/highlighting.spl` | 4 | 0 | highlight_comments, highlight_keywords, highlight_numbers, highlight_strings |
| `src/compiler/10.frontend/core/interpreter/interp_resource_tracker.spl` | 4 | 0 | irt_begin_module, irt_init, irt_track_func_owned, irt_unload_module |
| `src/compiler/00.common/dependency/resolution.spl` | 4 | 0 | resolve, resolve_segment_with_numbering, to_dir_path, to_file_path |
| `src/app/io/dir_ops.spl` | 4 | 4 | dir_list, dir_remove, dir_walk, is_dir |
| `src/app/devhub/cmd_bb.spl` | 4 | 0 | _bb_parse_int, _bb_resolve_limit, _bb_resolve_repo, _bb_resolve_workspace |
| `test/fixtures/storage/dbfs/bench_harness.spl` | 3 | 0 | make_fat32_table, make_ramfs_table, run_all |
| `test/fixtures/app/llm_caret/distributed_authority_verification_fixture_v2.spl` | 3 | 0 | verification_bytes, verification_key, verification_seed |
| `src/lib/nogc_sync_mut/lazy_val.spl` | 3 | 3 | get_lazy_stats, lazy, reset_lazy_stats |
| `src/lib/nogc_sync_mut/env/variables.spl` | 3 | 0 | env_clear, env_restore, env_snapshot |
| `src/lib/nogc_sync_mut/database/bug.spl` | 3 | 0 | bug_database_from_sdn, bug_shard_dir, load_bug_database_checked |
| `src/lib/nogc_async_mut/ndarray/mod.spl` | 3 | 0 | array, array_bool, array_i64 |
| `src/lib/nogc_async_mut/lazy_val.spl` | 3 | 3 | get_lazy_stats, lazy, reset_lazy_stats |
| `src/lib/gc_async_mut/lazy_val.spl` | 3 | 3 | get_lazy_stats, lazy, reset_lazy_stats |
| `src/lib/common/yaml/types.spl` | 3 | 0 | yaml_get_scalar_type, yaml_mapping, yaml_sequence |
| `src/lib/common/task_runner/distributed_operation_journal_v2.spl` | 3 | 3 | distributed_operation_journal_close_v2, distributed_operation_journal_open_v2, distributed_operation_journal_recover_execution_v2 |
| `src/compiler_rust/lib/std/src/sys/env.spl` | 3 | 3 | cwd, get, set |
| `src/compiler_rust/lib/std/src/spec/screenshot.spl` | 3 | 3 | get_screenshot_path, screenshot_exists, screenshot_markdown |
| `src/compiler_rust/lib/std/src/spec/feature_doc.spl` | 3 | 3 | generate_feature_doc, generate_master_index, register_feature |
| `src/compiler_rust/lib/std/src/spec/diagram.spl` | 3 | 3 | generate_arch_diagram, generate_class_diagram, generate_sequence |
| `src/compiler_rust/lib/std/src/core/time.spl` | 3 | 3 | days_between, now_iso8601, now_timestamp |
| `src/compiler_rust/lib/std/src/core/decorators.spl` | 3 | 3 | cached, deprecated, logged |
| `src/compiler_rust/lib/std/src/concurrency/threads.spl` | 3 | 3 | available_parallelism, spawn_isolated_with_args, spawn_limited |
| `src/compiler/90.tools/duplicate_check/formatter.spl` | 3 | 3 | print_json_report, print_text_report, write_sdn_database |
| `src/compiler/90.tools/duplicate_check/config.spl` | 3 | 1 | compute_config_hash, load_config, parse_config_file |
| `src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl` | 3 | 0 | mir_storage_address_recipe_v1, mir_storage_view_binding_v1, mir_storage_view_site_binding_v1 |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | 3 | 0 | create_alignment_check_block, create_peeling_block, create_vector_loop_block |
| `src/compiler/50.mir/mir_instruction_support.spl` | 3 | 3 | mir_call_origin_text, mir_call_origin_uses_local_symbols, mir_call_origin_uses_local_symbols_named |
| `src/compiler/35.semantics/macro_contracts.spl` | 3 | 0 | macrocontractresult_empty, process_macro_contract, symbolscope_empty |
| `src/compiler/15.blocks/blocks/builder.spl` | 3 | 0 | blockbuilder_new, blockbuilder_parser, blockbuilder_simple_parser |
| `src/compiler/10.frontend/core/type_subst.spl` | 3 | 0 | subst_type_in_decl, type_subst_add, type_subst_reset |
| `src/compiler/10.frontend/core/parser.spl` | 3 | 1 | parser_warn, parser_warnings_clear, parser_warnings_get |
| `src/compiler/10.frontend/core/interpreter/eval.spl` | 3 | 0 | eval_control_condition, eval_reset, match_enum_variant_pattern |
| `src/compiler/10.frontend/core/ast_stmt.spl` | 3 | 0 | stmt_block_stmt, stmt_match_stmt, stmt_return_stmt |
| `src/app/ui.render/fmt.spl` | 3 | 3 | pad_center, pad_left, pad_right |
| `src/app/llm_caret/workbench/distributed_grant_verification_v2.spl` | 3 | 3 | distributed_authority_key_check_v2, distributed_signature_bytes_v2, distributed_verify_grant_approval_v2 |
| `src/app/bug/workaround_store.spl` | 3 | 0 | workaround_fullscan_args, workaround_limit_from_env, workaround_status_args |
| `test/system/reftest/parity/pixel_diff.spl` | 2 | 0 | compare_pictures, compare_with_threshold |
| `test/system/reftest/parity/harness.spl` | 2 | 0 | reftest_harness_new, scene_signature |
| `test/perf/graphics_2d/bench_harness.spl` | 2 | 0 | make_bench_frame_record, write_report |
| `test/helpers/backend_render_record_fixture.spl` | 2 | 0 | backend_render_fixture, backend_render_fixture_replace |
| `test/fixtures/fonts/simple_2d_vector/font_fixture.spl` | 2 | 0 | simple_2d_ascii_font_bytes, simple_2d_latin1_font_bytes |
| `test/fixtures/compiler/rti_alias_ownership/src/compiler/10.frontend/core/provider.spl` | 2 | 0 | identity, ordinary |
| `test/fixtures/compiler/macro_array_insert_native.spl` | 2 | 0 | macro_insert_boundary_check, macro_sorted_names_check |
| `test/fixtures/compiler/llvm_aggregate_trace_native.spl` | 2 | 0 | llvm_aggregate_count_boundary_case, llvm_aggregate_trace_case |
| `test/fixtures/compiler/database_optional_receiver_prefix_probe.spl` | 2 | 0 | db_optional_mutation_probe_v1, db_query_prefix_probe_v1 |
| `src/plugins/backend_lean/lean_mir_translate.spl` | 2 | 0 | lean_runtime_name, translate_direct_call_callee |
| `src/os/kernel/boot/mmio_hardware.spl` | 2 | 2 | hardware_mmio_read64, hardware_mmio_write64 |
| `src/lib/nogc_sync_mut/test_runner/doctest_runner.spl` | 2 | 1 | _dt_failure_reason, run_spl_doctests_same_file |
| `src/lib/nogc_sync_mut/sffi/system.spl` | 2 | 2 | sffi_env_vars, sffi_process_wait |
| `src/lib/nogc_sync_mut/sffi/host.spl` | 2 | 0 | tls13_aes128_gcm_decrypt, tls13_aes128_gcm_decrypt_decode |
| `src/lib/nogc_sync_mut/package/semver.spl` | 2 | 2 | parse_constraint, parse_version |
| `src/lib/nogc_sync_mut/mcp/jj/tools_jj.spl` | 2 | 2 | get_all_jj_tool_schemas, handle_jj_tool |
| `src/lib/nogc_sync_mut/mcp/jj/tools_git.spl` | 2 | 2 | get_all_git_tool_schemas, handle_git_tool |
| `src/lib/nogc_sync_mut/mcp/jj/resources.spl` | 2 | 2 | get_all_resources, read_resource |
| `src/lib/nogc_sync_mut/mcp/jj/prompts.spl` | 2 | 2 | get_all_prompts, get_prompt |
| `src/lib/nogc_sync_mut/io/file_ops.spl` | 2 | 2 | file_hardlink, file_seal_readonly |
| `src/lib/nogc_sync_mut/daemon_sdk/lock.spl` | 2 | 2 | release_daemon_lock_owned, try_acquire_daemon_lock_owned |
| `src/lib/nogc_sync_mut/benchmark/measure.spl` | 2 | 2 | get_timestamp, time_function |
| `src/lib/nogc_async_mut/package/semver.spl` | 2 | 2 | parse_constraint, parse_version |
| `src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl` | 2 | 0 | aes128_gcm_decrypt, aes128_gcm_encrypt |
| `src/lib/nogc_async_mut_noalloc/baremetal/x86/boot_impl.spl` | 2 | 0 | vga_clear, vga_write_string |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl` | 2 | 0 | uart_init, uart_puts |
| `src/lib/nogc_async_mut/mcp/jj/tools_jj.spl` | 2 | 2 | get_all_jj_tool_schemas, handle_jj_tool |
| `src/lib/nogc_async_mut/mcp/jj/tools_git.spl` | 2 | 2 | get_all_git_tool_schemas, handle_git_tool |
| `src/lib/nogc_async_mut/mcp/jj/resources.spl` | 2 | 2 | get_all_resources, read_resource |
| `src/lib/nogc_async_mut/mcp/jj/prompts.spl` | 2 | 2 | get_all_prompts, get_prompt |
| `src/lib/nogc_async_mut/database/bug.spl` | 2 | 0 | bug_shard_dir, load_bug_database_checked |
| `src/lib/nogc_async_mut/benchmark/measure.spl` | 2 | 2 | get_timestamp, time_function |
| `src/lib/gc_async_mut/package/semver.spl` | 2 | 2 | parse_constraint, parse_version |
| `src/lib/gc_async_mut/benchmark/measure.spl` | 2 | 2 | get_timestamp, time_function |
| `src/lib/common/structural/transfer/transfer_contracts.spl` | 2 | 2 | parallel_transfer_mode_to_u8, parallel_transfer_payload_to_u8 |
| `src/compiler_rust/lib/std/src/verification/lean/runner.spl` | 2 | 2 | check_lean_file, is_lean_installed |
| `src/compiler_rust/lib/std/src/spec/progress.spl` | 2 | 2 | init_progress, reset_progress |
| `src/compiler_rust/lib/std/src/spec/formatters/json.spl` | 2 | 2 | print_json_results, write_json_results |
| `src/compiler_rust/lib/std/src/cli_output/_test_mut.spl` | 2 | 0 | test_no_mutate, test_with_mutate |
| `src/compiler_rust/lib/std/src/cli_output/_test_array_init.spl` | 2 | 0 | test_i64_arr, test_text_arr |
| `src/compiler_rust/lib/std/src/cli_output/buffer.spl` | 2 | 0 | buffer_start, log_print |
| `src/compiler/95.interp/interpreter/llvm/target.spl` | 2 | 0 | detect_host_arch_string, detect_host_os_string |
| `src/compiler/90.tools/verify/noalloc_manifest_scan.spl` | 2 | 2 | run_noalloc_manifest_scan, scan_noalloc_functions |
| `src/compiler/90.tools/duplicate_check/semantic_formatter.spl` | 2 | 2 | print_semantic_json_report, print_semantic_text_report |
| `src/compiler/80.driver/shb/shb_hash.spl` | 2 | 0 | shb_find_fn, shb_source_hash |
| `src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl` | 2 | 0 | sb_callee_name, sb_fn_operand |
| `src/compiler/60.mir_opt/mir_opt/storage_simd_admission.spl` | 2 | 0 | storage_simd_admission_v1, storage_simd_admit |
| `src/compiler/60.mir_opt/mir_opt/storage_layout_access_advisory.spl` | 2 | 0 | storage_layout_access_advisory_v1, storage_layout_access_advisory_with_memory_policy_v1 |
| `src/compiler/60.mir_opt/mir_opt/loop_strength.spl` | 2 | 0 | create_strength_reduction_pass, strength_reduction_provider |
| `src/compiler/60.mir_opt/mir_opt/dce.spl` | 2 | 0 | create_dce_pass, dce_instruction_is_mandatory_observation |
| `src/compiler/60.mir_opt/mir_opt/collection_opt.spl` | 2 | 0 | collection_opt_run_on_function, create_collection_opt_pass |
| `src/compiler/50.mir/mir_lowering_stmts.spl` | 2 | 2 | hir_type_is_declared_float_slot, hir_unsuffixed_int_literal_value |
| `src/compiler/35.semantics/semantics/cast_rules.spl` | 2 | 0 | cast_float_to_numeric, cast_int_to_numeric |
| `src/compiler/35.semantics/macro_check/mod.spl` | 2 | 0 | macrocall_create, macrorule_create |
| `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl` | 2 | 0 | hir_dependency_is_builtin_type, hir_payload_origin_miss_key |
| `src/compiler/15.blocks/blocks/error_helpers.spl` | 2 | 0 | error_at, error_span |
| `src/compiler/15.blocks/blocks/easy.spl` | 2 | 2 | define_block, define_const_block |
| `src/compiler/10.frontend/core/lexer.spl` | 2 | 0 | lex_env_i64, lex_snapshot_restore |
| `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` | 2 | 0 | module_resolve_cache_reset, module_resolve_uncached_count |
| `src/compiler/10.frontend/core/interpreter/eval_decls.spl` | 2 | 0 | eval_init, match_fallthrough_profile_is_deny |
| `src/compiler/10.frontend/core/cfg_platform.spl` | 2 | 0 | cfg_triple_arch, cfg_triple_os |
| `src/app/portal/services/auth_service.spl` | 2 | 2 | find_user_by_id, verify_api_token |
| `src/app/mcpgdb/json_helpers.spl` | 2 | 0 | make_tool_error, make_tool_result |
| `src/app/io/sffi_common.spl` | 2 | 2 | is_invalid_handle, is_valid_handle |
| `src/app/io/crypto_sffi.spl` | 2 | 2 | hmac_sha256, random_hex |
| `src/app/devhub/gui_server.spl` | 2 | 0 | _devhub_gui_status_text, run_devhub_gui |
| `src/app/devhub/cmd_git.spl` | 2 | 0 | _parse_i64, _parse_i64_or |
| `test/system/reftest/parity/scenes/transform_tree.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/text_arabic.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/scroll_damage.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/porter_duff.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/path_winding.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/path_evenodd.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/opacity_layer.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/mix_blend_mode.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/gradient_linear.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/dashed_strokes.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/scenes/backdrop_filter.spl` | 1 | 0 | scene |
| `test/system/reftest/parity/goldens/transform_tree_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/text_arabic_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/scroll_damage_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/porter_duff_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/path_winding_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/path_evenodd_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/opacity_layer_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/mix_blend_mode_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/gradient_linear_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/dashed_strokes_golden.spl` | 1 | 0 | probes |
| `test/system/reftest/parity/goldens/backdrop_filter_golden.spl` | 1 | 0 | probes |
| `test/helpers/simpleos_render_evidence_fixture.spl` | 1 | 0 | simpleos_target_evidence |
| `test/fixtures/url_query_contract/checks.spl` | 1 | 0 | url_query_contract_checks_v1 |
| `test/fixtures/parser_import_newline/escape_target.spl` | 1 | 0 | escape_candidate |
| `test/fixtures/native_build_closure/src/os/kernel/memory/swap.spl` | 1 | 0 | fixture_swap |
| `test/fixtures/native_build_closure/src/os/kernel/memory/manager.spl` | 1 | 0 | fixture_manager |
| `test/fixtures/native_build_closure/src/os/kernel/memory/capabilities.spl` | 1 | 0 | fixture_capabilities |
| `test/fixtures/native_build_closure/src/os/kernel/memory/adapters.spl` | 1 | 0 | fixture_adapters |
| `test/fixtures/native_build_closure/src/lib/nogc_sync_mut/explicit_fixture.spl` | 1 | 0 | fixture_explicit |
| `test/fixtures/native_build_closure/src/compiler/80.driver/driver.spl` | 1 | 0 | fixture_driver |
| `test/fixtures/compiler/tldr_future_binding_native.spl` | 1 | 0 | tldr_future_binding_check |
| `test/fixtures/compiler/phase2_native_repro/hist_rec.spl` | 1 | 0 | make_hist |
| `test/fixtures/compiler/native_array_return_record_owner/provider.spl` | 1 | 0 | all_batches |
| `test/fixtures/buildrunner/remote_authority_v1.spl` | 1 | 0 | remote_authority_fixture_v1 |
| `test/fixtures/arch_check/src/core/lexer.spl` | 1 | 1 | tokenize |
| `test/03_system/feature/app/remote_baremetal/remote_baremetal_library_workload.spl` | 1 | 0 | run_baremetal_library_workload |
| `test/01_unit/compiler/dup_struct_name/case_three_variants/m2.spl` | 1 | 0 | mk2 |
| `test/01_unit/compiler/dup_struct_name/case_three_variants/m1.spl` | 1 | 0 | mk1 |
| `test/01_unit/compiler/dup_struct_name/case_param_field_read/m2.spl` | 1 | 0 | mk2 |
| `test/01_unit/compiler/dup_struct_name/case_param_field_read/m1.spl` | 1 | 0 | mk1 |
| `test/01_unit/compiler/dup_struct_name/case_identical_layout/m2.spl` | 1 | 0 | mk2 |
| `test/01_unit/compiler/dup_struct_name/case_identical_layout/m1.spl` | 1 | 0 | mk1 |
| `test/01_unit/compiler/dup_struct_name/case_class_vs_struct/m2.spl` | 1 | 0 | mk2 |
| `test/01_unit/compiler/dup_struct_name/case_class_vs_struct/m1.spl` | 1 | 0 | mk1 |
| `src/plugins/backend_llvm_lib/llvm_lib_translate_expr.spl` | 1 | 0 | llvm_lib_named_call_symbol |
| `src/os/tls13/record13.spl` | 1 | 0 | record13_decrypt_fd |
| `src/os/kernel/arch_adapt/x86_64/mod.spl` | 1 | 1 | create_x86_64_hal_adapter |
| `src/os/crypto/chacha20.spl` | 1 | 0 | chacha20_block |
| `src/lib/scv/compile_snapshot.spl` | 1 | 0 | scv_compile_snapshot_bytes_match_v1 |
| `src/lib/nogc_sync_mut/websocket/handshake.spl` | 1 | 0 | base64_encode_bytes |
| `src/lib/nogc_sync_mut/ui_test/sgtti.spl` | 1 | 0 | sgtti_node_geometry |
| `src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl` | 1 | 1 | easy_fix_check_short_grammar_refactor |
| `src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl` | 1 | 0 | discover_sdoctest_files_for_path_run |
| `src/lib/nogc_sync_mut/sffi/runtime.spl` | 1 | 0 | transient_array_scope_identity_v1 |
| `src/lib/nogc_sync_mut/sffi/process_capture.spl` | 1 | 0 | process_capture_result |
| `src/lib/nogc_sync_mut/sffi/math.spl` | 1 | 0 | random_i64_raw |
| `src/lib/nogc_sync_mut/io/tls_common_hooks.spl` | 1 | 1 | tls_hook_bytes_to_text |
| `src/lib/nogc_sync_mut/io/debug_stubs.spl` | 1 | 1 | rt_debug_remove_all_breakpoints |
| `src/lib/nogc_sync_mut/engine/physics/query/overlap.spl` | 1 | 0 | circle_overlap_2d |
| `src/lib/nogc_async_mut/websocket/upgrade.spl` | 1 | 0 | compute_accept_value |
| `src/lib/nogc_async_mut/torch/mod.spl` | 1 | 1 | cuda_available |
| `src/lib/nogc_async_mut/slang/nvfs_client/std_fs.spl` | 1 | 1 | publish_staged |
| `src/lib/nogc_async_mut/sanitizer/types.spl` | 1 | 1 | san_event |
| `src/lib/nogc_async_mut_noalloc/tls/x25519.spl` | 1 | 1 | x25519 |
| `src/lib/nogc_async_mut_noalloc/baremetal/arm/startup.spl` | 1 | 0 | enable_interrupts |
| `src/lib/nogc_async_mut/http_client/types.spl` | 1 | 1 | parse_url |
| `src/lib/nogc_async_mut/engine/physics/query/raycast2d.spl` | 1 | 0 | raycast_2d |
| `src/lib/nogc_async_mut/engine/physics/query/overlap.spl` | 1 | 0 | circle_overlap_2d |
| `src/lib/gc_async_mut/slang/model_executor/model_loader/manifest.spl` | 1 | 0 | _array_body |
| `src/lib/gc_async_mut/sanitizer/types.spl` | 1 | 1 | san_event |
| `src/lib/common/yaml/parse.spl` | 1 | 0 | yaml_parse |
| `src/lib/common/use_warning_probe.spl` | 1 | 1 | uw_probe_plain_provided |
| `src/lib/common/structural/transfer/process_frame_codec.spl` | 1 | 1 | process_transfer_frame_header_len |
| `src/lib/common/contracts/distributed_control_v2.spl` | 1 | 1 | distributed_grant_authorize_v2 |
| `src/lib/common/contracts/distributed_control_codec_v2.spl` | 1 | 0 | distributed_encode_grant_v2 |
| `src/compiler_rust/lib/std/src/verification/lean/memory_safety.spl` | 1 | 1 | generate_memory_safety_lean |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl` | 1 | 1 | collect_vcs_state |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/todo_collector.spl` | 1 | 1 | collect_todos |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/spipe_collector.spl` | 1 | 1 | collect_spipe_tests |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/plan_collector.spl` | 1 | 1 | collect_plans |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/coverage_collector.spl` | 1 | 1 | collect_coverage |
| `src/compiler_rust/lib/std/src/tooling/config_env.spl` | 1 | 1 | get_env_vars |
| `src/compiler_rust/lib/std/src/tooling/brief_view.spl` | 1 | 1 | extract_brief_from_file |
| `src/compiler_rust/lib/std/src/sys/args.spl` | 1 | 1 | args |
| `src/compiler_rust/lib/std/src/spec/formatters/progress.spl` | 1 | 1 | print_progress_results |
| `src/compiler_rust/lib/std/src/spec/formatters/doc.spl` | 1 | 1 | print_doc_results |
| `src/compiler_rust/lib/std/src/sdn/parser.spl` | 1 | 1 | parse |
| `src/compiler_rust/lib/std/src/sdn/lexer.spl` | 1 | 0 | tokenize |
| `src/compiler_rust/lib/std/src/host/async_gc_mut/io/fs/file.spl` | 1 | 1 | exist |
| `src/compiler/99.loader/module_resolver/resolution.spl` | 1 | 0 | normalize_type_segments |
| `src/compiler/99.loader/loader/smf_reloc_partition.spl` | 1 | 0 | smf_partition_code_relocations_v1 |
| `src/compiler/95.interp/interpreter/llvm/tools.spl` | 1 | 0 | llc_available |
| `src/compiler/90.tools/verify/noalloc_reachable.spl` | 1 | 1 | print_noalloc_reachable_imports |
| `src/compiler/90.tools/fix/rules/impl_/lint_code.spl` | 1 | 0 | check_non_exhaustive_match_with_lines |
| `src/compiler/85.mdsoc/feature/codegen/backends/interpreter/backend.spl` | 1 | 0 | create_interpreter_backend |
| `src/compiler/80.driver/smf_elf_parser.spl` | 1 | 0 | elf_relocated_non_code_section |
| `src/compiler/80.driver/shb/shb_writer.spl` | 1 | 0 | shb_write |
| `src/compiler/80.driver/shb/shb_extractor.spl` | 1 | 0 | extract_symbol_hashes |
| `src/compiler/80.driver/managed_parse_group.spl` | 1 | 0 | managed_parse_group_feature_identity_v1 |
| `src/compiler/80.driver/driver_mem_snapshot.spl` | 1 | 0 | mem_snapshot_owner_v1 |
| `src/compiler/80.driver/driver_hir_cache.spl` | 1 | 0 | hir_cache_reload_body_v1 |
| `src/compiler/80.driver/driver_build/incremental.spl` | 1 | 0 | native_build_compiler_exe_candidates_v1 |
| `src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl` | 1 | 0 | local_count_increment |
| `src/compiler/60.mir_opt/mir_opt/typed_byte_canon.spl` | 1 | 0 | create_typed_byte_canon_pass |
| `src/compiler/60.mir_opt/mir_opt/storage_simd_schedule.spl` | 1 | 0 | storage_simd_schedule |
| `src/compiler/60.mir_opt/mir_opt/storage_simd_codegen.spl` | 1 | 0 | storage_simd_emit_full_block |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | 1 | 0 | cipher_rule_provider |
| `src/compiler/60.mir_opt/mir_opt/const_fold.spl` | 1 | 0 | create_const_fold_pass |
| `src/compiler/60.mir_opt/mir_opt/collection_opt_patterns.spl` | 1 | 0 | colopt_match_concat_pattern |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` | 1 | 0 | detect_bounds_from_block |
| `src/compiler/50.mir/synthetic_driver_codegen.spl` | 1 | 0 | make_register_static_driver_call |
| `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 1 | 0 | hir_type_instantiates_to |
| `src/compiler/50.mir/hir_declaration_summary_v1.spl` | 1 | 1 | mir_hir_project_encoded_module_in_owned_scope_v1 |
| `src/compiler/35.semantics/lint/return_type_mismatch.spl` | 1 | 1 | check_return_type_mismatch |
| `src/compiler/35.semantics/lint/collection_patterns.spl` | 1 | 0 | coll006_severity_for_profile |
| `src/compiler/15.blocks/blocks/text_transforms.spl` | 1 | 0 | strip_indent |
| `src/compiler/15.blocks/blocks/context.spl` | 1 | 0 | blockerror_parse |
| `src/compiler/10.frontend/core/tokens.spl` | 1 | 0 | tok_is_additive |
| `src/compiler/10.frontend/core/lexer_struct.spl` | 1 | 0 | make_core_lexer_char_mode |
| `src/compiler/10.frontend/core/interpreter/jit.spl` | 1 | 0 | jit_init |
| `src/compiler/10.frontend/core/interpreter/eval_calls.spl` | 1 | 0 | eval_function_call |
| `src/compiler/10.frontend/core/closure_analysis.spl` | 1 | 0 | closure_warnings_clear |
| `src/compiler/10.frontend/core/call_graph.spl` | 1 | 0 | call_graph_warnings_clear |
| `src/compiler/10.frontend/core/_Ast/module_state.spl` | 1 | 0 | module_get_decls |
| `src/compiler/10.frontend/core/_AstExpr/nodes.spl` | 1 | 0 | expr_reset |
| `src/compiler/00.common/module_path_naming.spl` | 1 | 0 | _module_path_naming_text_index_of |
| `src/compiler/00.common/dependency/graph.spl` | 1 | 1 | importgraph_find_cycles |
| `src/compiler/00.common/assurance/warning_phase.spl` | 1 | 1 | phased_rule_severity_rank |
| `src/app/ui.render/_TuiWidgets/extended_widgets.spl` | 1 | 0 | tui_active_index_or_default |
| `src/app/ui.render/_TuiWidgets/core_widgets.spl` | 1 | 0 | tui_int_or |
| `src/app/test_runner_new/doctest_runner.spl` | 1 | 0 | extract_doctests |
| `src/app/test/engine_differential_contract.spl` | 1 | 1 | differential_terminal_newline |
| `src/app/spec_gen/main.spl` | 1 | 0 | extract_quoted |
| `src/app/sj_daemon/forbidden.spl` | 1 | 0 | check_forbidden |
| `src/app/portal/models/user.spl` | 1 | 1 | new_user |
| `src/app/portal/models/api_token.spl` | 1 | 1 | new_api_token |
| `src/app/llm_caret/claude_full/utils/displayTags.spl` | 1 | 1 | stripDisplayTags |
| `src/app/devhub/errors.spl` | 1 | 0 | itf_error_from_http |
| `src/app/devhub/cmd_minio.spl` | 1 | 0 | _require_auth |
| `src/app/devhub/cmd_api.spl` | 1 | 0 | handle_api |
| `src/app/cli/query_outline.spl` | 1 | 0 | parse_outline_source |

## Appendix A - rule 1 scan

```sh
#!/bin/sh
# Static census of braced `use m.{name}` imports that the seed's private-import
# rule rejects (module_loader.rs check_private_use_names):
#   - `name` is a top-level fn with Private visibility (bare `fn`/`async fn`)
#   - not re-exposed by an `export` statement in the defining module
#   - importer file lives in a different directory than the defining module
#   - (definer-relpath|name) not frozen in scripts/check/private_import_baseline.txt
# Resolution is name+path-suffix based (last two module segments, NN. layer
# prefixes stripped, __init__/mod as package files). Output TSV:
#   importer<TAB>definer<TAB>name
# Usage: sh scan-private-cross-dir-imports.shs <repo_root> [roots...]
set -eu
root=${1:?repo root}
shift || true
[ $# -gt 0 ] || set -- src test scripts
cd "$root"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
find "$@" -name '*.spl' -type f -not -path '*/vendor/*' -print0 > "$tmp/files"
# Pass 1: facts.
xargs -0 awk '
function flushuse(   s, mp, body, n, i, parts, nm) {
  s = acc; acc = ""; inuse = 0
  if (s !~ /\{/) return
  if (eraw) { eacc = s; sub(/^[^{]*\{/, "", eacc); flushexp(); eraw = 0 }
  mp = s; sub(/^[ \t]*(export[ \t]+)?use[ \t]+/, "", mp); sub(/\.?\{.*/, "", mp); gsub(/[ \t]/, "", mp)
  body = s; sub(/^[^{]*\{/, "", body); sub(/\}.*/, "", body)
  n = split(body, parts, ",")
  for (i = 1; i <= n; i++) {
    nm = parts[i]; gsub(/^[ \t\r\n]+|[ \t\r\n]+$/, "", nm); sub(/[ \t]+as[ \t].*/, "", nm)
    if (nm ~ /^[A-Za-z_][A-Za-z0-9_]*$/) print "U\t" FILENAME "\t" mp "\t" nm "\t" ukind
  }
}
function flushexp(   s, n, i, parts, nm) {
  s = eacc; eacc = ""; inexp = 0
  gsub(/[{},.*]/, " ", s)
  n = split(s, parts, /[ \t]+/)
  for (i = 1; i <= n; i++) { nm = parts[i]; if (nm ~ /^[A-Za-z_][A-Za-z0-9_]*$/) print "E\t" FILENAME "\t" nm }
}
FNR == 1 { if (inuse) flushuse(); if (inexp) flushexp(); print "F\t" FILENAME }
{
  line = $0; sub(/#.*/, "", line)
  if (inuse) { acc = acc " " line; if (line ~ /\}/) flushuse(); next }
  if (inexp) { eacc = eacc " " line; if (line ~ /\}/) flushexp(); next }
  if (line ~ /^[ \t]*use[ \t]+[A-Za-z_]/ || line ~ /^export[ \t]+use[ \t]+[A-Za-z_][A-Za-z0-9_.]*\.?\{/) { if (line ~ /^export/) { ukind = "export"; eacc = line; sub(/^[^{]*\{/, "", eacc); eraw = 1 } else { ukind = "use"; eraw = 0 }; acc = line; inuse = 1; if (line !~ /\{/ || line ~ /\}/) flushuse(); next }
  if (line ~ /^export[ \t]/ && line !~ /^export[ \t]+(fn|struct|class|enum|trait|val|var|type|impl|extern|async)[ \t]/) {
    eacc = line; sub(/^export[ \t]+(use[ \t]+)?/, "", eacc)
    # keep only the braced list (or bare names) - drop the module path
    if (eacc ~ /\{/) { sub(/^[^{]*\{/, "", eacc) } else if (line ~ /^export[ \t]+use[ \t]/) { sub(/^.*\./, "", eacc) }
    inexp = 1; if (line !~ /\{/ || line ~ /\}/) flushexp(); next
  }
  if (line ~ /^(async[ \t]+)?fn[ \t]+[A-Za-z_]/) {
    nm = line; sub(/^(async[ \t]+)?fn[ \t]+/, "", nm); sub(/[^A-Za-z0-9_].*/, "", nm)
    print "D\t" FILENAME "\tpriv\t" nm
  } else if (line ~ /^(pub|export)[ \t]+(async[ \t]+)?fn[ \t]+[A-Za-z_]/) {
    nm = line; sub(/^(pub|export)[ \t]+(async[ \t]+)?fn[ \t]+/, "", nm); sub(/[^A-Za-z0-9_].*/, "", nm)
    print "D\t" FILENAME "\tpub\t" nm
  }
}
END { if (inuse) flushuse(); if (inexp) flushexp() }
' < "$tmp/files" > "$tmp/facts"
# Pass 2: resolve.
# Pass 2: resolve each module path to the file(s) the loader picks: longest
# trailing segment match (NN. layer prefixes stripped); `x.spl` beats
# `x/mod.spl` / `x/__init__.spl` at equal match length.
awk -F'\t' -v BL="scripts/check/private_import_baseline.txt" '
function key(f,   k) { k = f; sub(/\.spl$/, "", k); sub(/\/(__init__|mod)$/, "", k); gsub(/\/[0-9][0-9]\./, "/", k); return k }
function dir(f) { sub(/\/[^\/]*$/, "", f); return f }
function pkgfile(f) { return f ~ /\/(__init__|mod)\.spl$/ }
BEGIN { while ((getline l < BL) > 0) { gsub(/^[ \t]+|[ \t]+$/, "", l); if (l != "") bl[l] = 1 } }
NR == FNR {
  if ($1 == "F") { k = key($2); n = split(k, p, "/"); bylast[p[n]] = bylast[p[n]] "\034" $2 }
  else if ($1 == "D") vis[$2 SUBSEP $4] = $3
  else if ($1 == "E") exp_[$2 SUBSEP $3] = 1
  next
}
$1 == "U" {
  ms = $3
  if (!(ms in res)) {
    n = split(ms, s, "."); m = split(bylast[s[n]], c, "\034"); bestn = 0; out = ""; bestspl = 0
    for (i = 2; i <= m; i++) {
      kn = split(key(c[i]), kp, "/"); j = 0
      while (j < n && j < kn && kp[kn - j] == s[n - j]) j++
      if (j < n && j < 2 && n >= 2) continue
      isspl = !pkgfile(c[i])
      if (j > bestn || (j == bestn && isspl && !bestspl)) { bestn = j; out = "\034" c[i]; bestspl = isspl }
      else if (j == bestn && isspl == bestspl) out = out "\034" c[i]
    }
    res[ms] = out
  }
  m = split(res[ms], c, "\034")
  for (i = 2; i <= m; i++) {
    f = c[i]
    if (vis[f SUBSEP $4] != "priv") continue
    if ((f SUBSEP $4) in exp_) continue
    if (dir(f) == dir($2)) continue
    if ((f "|" $4) in bl) continue
    print $2 "\t" f "\t" $4 "\t" $5
  }
}
' "$tmp/facts" "$tmp/facts" | sort -u
```

## Appendix B - rule 2 scan (glob-import calls, unvalidated)

```sh
#!/bin/sh
# Rule 2 census (module_loader.rs check_private_call_visibility): a non-test
# caller that reaches a private fn of another directory's module through a
# glob import (`use m.*`) and calls it. Test callers are exempt in the seed.
# Output TSV: caller<TAB>definer<TAB>name   (baseline pairs excluded)
# Usage: sh scan-private-glob-calls.shs <repo_root> [roots...]
set -eu
root=${1:?repo root}
shift || true
[ $# -gt 0 ] || set -- src scripts
cd "$root"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
find src test scripts -name '*.spl' -type f -not -path '*/vendor/*' -print0 > "$tmp/all"
find "$@" -name '*.spl' -type f -not -path '*/vendor/*' -print0 > "$tmp/callers"
# definitions + exports over the whole tree
xargs -0 awk '
{ line = $0; sub(/#.*/, "", line) }
line ~ /^(async[ \t]+)?fn[ \t]+[A-Za-z_]/ { nm = line; sub(/^(async[ \t]+)?fn[ \t]+/, "", nm); sub(/[^A-Za-z0-9_].*/, "", nm); print "D\t" FILENAME "\t" nm; next }
line ~ /^export[ \t]/ && line !~ /^export[ \t]+(fn|struct|class|enum|trait|val|var|type|impl|extern|async)[ \t]/ {
  s = line; sub(/^export[ \t]+(use[ \t]+)?/, "", s); gsub(/[{},.*]/, " ", s); n = split(s, p, /[ \t]+/)
  for (i = 1; i <= n; i++) if (p[i] ~ /^[A-Za-z_][A-Za-z0-9_]*$/) print "E\t" FILENAME "\t" p[i]
}
' < "$tmp/all" > "$tmp/defs"
# glob uses + call tokens in callers that have a glob use
xargs -0 awk '
FNR == 1 { glob = 0; delete seen }
{ line = $0; sub(/#.*/, "", line) }
line ~ /^[ \t]*use[ \t]+[A-Za-z_][A-Za-z0-9_.]*\.\*/ { mp = line; sub(/^[ \t]*use[ \t]+/, "", mp); sub(/\.\*.*/, "", mp); print "G\t" FILENAME "\t" mp; glob = 1; next }
glob && line ~ /^(pub[ \t]+|export[ \t]+)?(async[ \t]+)?fn[ \t]/ { nm = line; sub(/^(pub[ \t]+|export[ \t]+)?(async[ \t]+)?fn[ \t]+/, "", nm); sub(/[^A-Za-z0-9_].*/, "", nm); print "L\t" FILENAME "\t" nm }
glob {
  s = line
  while (match(s, /[A-Za-z_][A-Za-z0-9_]*[ \t]*\(/)) {
    t = substr(s, RSTART, RLENGTH); sub(/[ \t]*\($/, "", t)
    pre = (RSTART > 1) ? substr(s, RSTART - 1, 1) : ""
    if (pre != "." && !(t in seen)) { seen[t] = 1; print "K\t" FILENAME "\t" t }
    s = substr(s, RSTART + RLENGTH)
  }
}
' < "$tmp/callers" > "$tmp/calls"
cat "$tmp/defs" "$tmp/calls" | awk -F'\t' -v BL="scripts/check/private_import_baseline.txt" '
function key(f,   k, n, i, p, out) {
  k = f; sub(/\.spl$/, "", k); sub(/\/(__init__|mod)$/, "", k)
  n = split(k, p, "/"); out = ""
  for (i = 1; i <= n; i++) { sub(/^[0-9][0-9]\./, "", p[i]); out = out "/" p[i] }
  return out
}
function dir(f) { sub(/\/[^\/]*$/, "", f); return f }
BEGIN { while ((getline l < BL) > 0) { gsub(/^[ \t]+|[ \t]+$/, "", l); if (l != "") bl[l] = 1 } }
$1 == "D" { priv[$2 SUBSEP $3] = 1; byname[$3] = byname[$3] "\034" $2; next }
$1 == "E" { ex[$2 SUBSEP $3] = 1; next }
$1 == "G" { n = split($3, s, "."); suf = (n >= 2) ? "/" s[n-1] "/" s[n] : "/" s[n]; globs[$2] = globs[$2] "\034" suf; next }
$1 == "L" { local[$2 SUBSEP $3] = 1; next }
$1 == "K" {
  if (!($3 in byname) || ($2 SUBSEP $3) in local) next
  m = split(byname[$3], c, "\034"); g = split(globs[$2], sf, "\034")
  for (i = 2; i <= m; i++) {
    f = c[i]; if ((f SUBSEP $3) in ex) continue
    if (dir(f) == dir($2)) continue
    if ((f "|" $3) in bl) continue
    k = key(f)
    for (j = 2; j <= g; j++) if (substr(k, length(k) - length(sf[j]) + 1) == sf[j]) { print $2 "\t" f "\t" $3; break }
  }
}
' | sort -u
```
