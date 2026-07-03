# BUG-TRACKING: Dead "only-compiled" spec tag — repo-wide sweep

Status: PARTIAL SWEEP COMPLETE (2026-07-03)

**Date:** 2026-07-03
**Context:** The tag `["only-compiled"]` is not recognized by any runner source
(`test_runner_files.spl` only understands `skip`/`pending`/`host`/`interpreter`/
`smf`/`native`/`composite`/`all`). Any `describe`/`it` block tagged
`only-compiled` silently collects 0/0 examples and reads as green while testing
nothing. Two canaries were already fixed in commit `aed81397b` (flat-AST specs:
0/0 → 2/2 and 3/3).

## Scope

`grep -rln '"only-compiled"' test/ src/` found 108 raw hits. After excluding
generated `.spipe_matchers_*` / `.spipe_wrapped_*` artifacts and one false
positive (`tag_parsing_spec.spl`, which uses the string `"only-compiled"` only
as literal test data for the tag parser itself, not as a real `tag: [...]`
directive), **106 real tagged files** remained, split roughly 1:1 between the
canonical numbered tree (`test/01_unit`, `test/02_integration`, `test/03_system`,
`test/05_perf` — 56 files) and legacy pre-renumbering mirror directories
(`test/unit`, `test/integration`, `test/feature`, `test/perf`, `test/system` —
50 files) that duplicate the same content byte-for-byte.

Given the ~40 minute budget, this pass processed the **56 canonical files**
only. The 50 legacy-mirror duplicates were not processed in this pass (same
files, same fate expected, but unverified — follow-up).

## Results (56 canonical files processed)

- **27 files: tag removed, now PASSES** — confirmed real, working specs that
  were dead-tagged for no reason. Kept un-tagged. **170 examples regained**
  (0 failures across all 27).
- **29 files: tag removed, but FAILS** — restored the tag immediately (repo
  rule: never leave newly-failing specs in the suite, never weaken/skip them).
  This is the valuable output: real latent failures hidden by the dead tag.
- **0 hangs**
- **0 edit failures** (tag removal always applied cleanly)

### 27 passing (tag removed, kept) — file :: examples passed

test/01_unit/compiler/mir/gpu_target_metadata_spec.spl :: 8
test/02_integration/baremetal/remote_riscv32_spec.spl :: 9
test/02_integration/compiler/llvm_compiled_proof_spec.spl :: 3
test/02_integration/compiler/vhdl_backend_e2e_spec.spl :: 2 (kept "slow" tag)
test/03_system/feature/usage/gpu_ptx_gen_spec.spl :: 3
test/03_system/feature/usage/llvm_backend_aarch64_spec.spl :: 11
test/03_system/feature/usage/llvm_backend_arm32_spec.spl :: 11
test/01_unit/lib/common/compatibility_spec.spl :: 8
test/03_system/feature/usage/llvm_backend_i686_spec.spl :: 11
test/01_unit/lib/common/parser_spec.spl :: 10
test/03_system/feature/usage/llvm_backend_riscv32_spec.spl :: 10
test/01_unit/lib/common/value_spec.spl :: 16
test/03_system/feature/usage/llvm_backend_riscv64_spec.spl :: 10
test/01_unit/sffi/sffi_public_api_spec.spl :: 2
test/05_perf/llvm_lib_ffi_perf_spec.spl :: 3
test/01_unit/std/parser_spec.spl :: 10
test/02_integration/io/native_ops_dir_create_spec.spl :: 1
test/03_system/feature/usage/btree_basic_spec.spl :: 7
test/03_system/feature/usage/cmm_lsp/bulk_validate_spec.spl :: 5
test/03_system/feature/usage/cmm_lsp/cmm_lexer_spec.spl :: 5
test/03_system/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl :: 3
test/03_system/feature/usage/cmm_lsp/cmm_parser_spec.spl :: 2
test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl :: 1
test/03_system/feature/usage/cmm_lsp/string_efficiency_spec.spl :: 9
test/03_system/feature/usage/contract_persistence_feature_spec.spl :: 1
test/03_system/feature/usage/hashmap_basic_spec.spl :: 8
test/05_perf/cli_dispatch_perf_spec.spl :: 1

Committed in 3 batches (9+10+8 files) on main:
`db46c93b94d`, `dfcd6a78500`, `009feed5eae5`.

### 29 restored-with-failures (tag left in place — FOLLOW-UP WORK LIST)

Each entry: file :: first failing example (from the untagged run before restore).

1. `test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl` — "consumes lane markers as queue-boundary accounting instead of unsupported instructions"
2. `test/01_unit/compiler/frontend/host_gpu_lane_structural_bridge_spec.spl` — "preserves target.later gpu lane metadata in rich AST"
3. `test/01_unit/compiler/hir/host_gpu_lane_hir_lowering_spec.spl` — "preserves target.later gpu lane metadata in HIR"
4. `test/01_unit/compiler/mir/host_gpu_lane_mir_marker_spec.spl` — "emits begin and end markers around target.later gpu lane body"
5. `test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl` — "turns lowered MIR lane markers into strict queue submission evidence"
6. `test/01_unit/compiler/parser/flat_ast_pub_decl_spec.spl` — "preserves GPU target decorators on the active frontend path"
7. `test/01_unit/compiler/parser/treesitter_error_recovery_spec.spl` — fails under "TreeSitter Error Recovery" describe
8. `test/02_integration/compiler/llvm_parity_spec.spl` — "compiles empty module via llvm"
9. `test/01_unit/compiler/parser/treesitter_highlights_spec.spl` — "extracts function with parameters for highlight"
10. `test/01_unit/compiler/parser/treesitter_incremental_spec.spl` — "reparses after adding a function"
11. `test/01_unit/compiler/parser/treesitter_spec.spl` — "parses single function"
12. `test/01_unit/compiler/parser/treesitter_visibility_spec.spl` — "parses scoped visibility on top-level declarations"
13. `test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl` — "filters entries without changing source map"
14. `test/03_system/feature/usage/llvm_backend_spec.spl` — "selects correct CPU for x86_64"
15. `test/02_integration/app/app_mcp_intensive_spec.spl` — "lists tools through the source-mode MCP server"
16. `test/02_integration/app/loader_exec_memory_spec.spl` — "maps executable memory and runs a tiny function"
17. `test/03_system/feature/usage/actor_model_spec.spl` — "creates spawn message with Vec3"
18. `test/03_system/feature/usage/cmm_lsp/cmm_v2025_spec.spl` — "config_for_version recognizes 2025"
19. `test/03_system/feature/usage/component_spec.spl` — "converts to string"
20. `test/03_system/feature/usage/math_autograd_runtime_spec.spl` — "computes gradients on requires_grad parameter"
21. `test/03_system/feature/usage/tensor_bridge_spec.spl` — "arrtens Vec3 list to array"
22. `test/03_system/feature/usage/tensor_spec.spl` — "is alias for Tensor<T, 2>"
23. `test/03_system/feature/usage/treesitter_cursor_spec.spl` — "parses fn declaration"
24. `test/03_system/feature/usage/treesitter_error_recovery_spec.spl` — "produces empty module for empty source"
25. `test/03_system/feature/usage/treesitter_lexer_spec.spl` — "tokenizes fn keyword"
26. `test/03_system/feature/usage/treesitter_parser_spec.spl` — "creates parser from source"
27. `test/03_system/feature/usage/treesitter_query_spec.spl` — "parses struct with type parameter"
28. `test/03_system/feature/usage/treesitter_tree_spec.spl` — "parses a simple function"
29. `test/03_system/quality/code_quality/allow_suppressions_spec.spl` — "AC-2: cli_dispatch_rust accepts named cmd args gc_log gc_off args"

Note the treesitter_* cluster (7 files) and host_gpu_lane_* cluster (5 files)
each look like they share one or two root causes rather than 12 independent
bugs — worth bisecting together as a follow-up.

## Not yet processed (follow-up)

- 50 legacy-mirror duplicate files under `test/unit/`, `test/integration/`,
  `test/feature/`, `test/perf/`, `test/system/` — same content as the 56
  canonical files above; expected same outcomes but unverified in this pass.
- `src/compiler/80.driver/**` and `src/compiler_rust/**` were explicitly
  excluded per task instructions (another agent's territory).

## Method

For each file: removed the `only-compiled` entry from its `tag: [...]` array
(dropping the whole clause when it was the only tag, keeping siblings like
`"slow"` otherwise), ran `timeout 300 bin/simple test <file>` (600s for known
heavy backend specs: llvm_backend*, vhdl_backend*, llvm_compiled_proof,
llvm_parity, remote_riscv32, gpu_ptx_gen, llvm_lib_ffi_perf). Passing files
were left untagged; failing files had the tag restored immediately (verified
via `git diff` producing no residual change).
