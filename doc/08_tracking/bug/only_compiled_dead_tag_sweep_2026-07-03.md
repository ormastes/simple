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

## Task #76 follow-up pass (items 8–29, non-treesitter/non-gpu-lane clusters)

Per-cluster triage of the restored-with-failures list. Verdicts:
**GATED** = tag kept/restored, blocker documented; **FIXED** = root-caused and
fixed at source, tag removed.

### map_traversal (item 13) — GATED (interpreter engine gap)

- Failure (all 4 examples): `semantic: method 'hash' not found on type 'i64'
  (receiver value: 1)` from `Map.insert` → `hash_key` → `key.hash()`.
- Root cause: the interpreter does not resolve `impl Hash for i64` (trait impl
  on a primitive, defined in `src/lib/nogc_sync_mut/src/hash.spl`) for method
  dispatch — a direct probe `use lib.nogc_sync_mut.src.hash.{Hash};
  (5 as i64).hash()` fails identically. The dispatch error is emitted from
  `src/compiler/80.driver/driver.spl` (forbidden path, other lane). Related:
  `use std.hash.Hash` from a spec reports `Module "std.hash" does not export
  'Hash'` (trait not `pub` / re-export gap).

### cmm_v2025 (item 18) — GATED (module unreachable by resolver)

- Failure (all 15 examples): `semantic: function 'config_for_version' not
  found` etc. — the spec's `use cmm_version.{...}` imports are commented out.
- Root cause: the implementation lives only at
  `examples/10_tooling/trace32_tools/cmm_lsp/*.spl`. No import path reaches it:
  `use examples.trace32_tools.cmm_lsp.cmm_version` → `Cannot resolve module`
  because the resolver's numbered-dir fallback (`find_numbered_dir`,
  `src/compiler/99.loader/module_resolver/resolution.spl`) only matches
  `NN.name`, not `NN_category/name`, and `10_tooling` cannot be spelled as an
  identifier segment. Sibling cmm specs pass only because they inline private
  mini-implementations. Fix requires a resolver feature or relocating the
  cmm_lsp example into an importable tree — out of sweep scope.

### component (item 19) — GATED (module never implemented)

- Failure (all examples): `semantic: variable 'ComponentType' not found` /
  `unsupported path call: ["ComponentManager", "create"]`.
- Root cause: spec is aspirational — `use game_engine.component` is commented
  out with "Module not yet implemented" and no such module exists anywhere in
  `src/`. Needs the game-engine component module to be written first.

### actor_model (item 17) — GATED (module never implemented)

- Failure (all examples): `method 'Vec3' not found on type 'dict'` (module-path
  constructor `math.Vec3(...)` in interpreter) and `unsupported path call:
  ["GameMessage", "Update"]`.
- Root cause: same as component — `use game_engine.actor_model` commented out,
  module does not exist; additionally interpreter path-call gaps on enum
  variants would block it even if it did.

### tensor_spec (item 22) — GATED (torch SFFI backend not wired + interpreter tensor method gaps)

- Failure (48/54 examples): `semantic: panic: torch SFFI backend not yet wired`
  (from stubs in `src/lib/nogc_sync_mut/src/tensor.spl` — sum/mean/prod eprint
  the same message), plus `unknown property or method 'T'/'mean'/'prod' on
  Array`, `sum` returning 0, transpose `'` operator losing bindings
  (`variable 'y' not found`).
- Root cause: the spec exercises tensor runtime ops (`use std.src.{Device,
  DType, zeros, ones}`) whose backend is explicitly stubbed as unwired; the
  interpreter also lacks the Array tensor extension methods. No describe block
  fully passes (checked per-describe), so whole-file tag restored. Needs the
  torch SFFI backend wiring — engine work, out of sweep scope.

### tensor_bridge (item 21) — GATED (interpreter module-path call gap)

- Failure (all 5 examples): `method 'Vec3' not found on type 'dict'` /
  `method 'tensor_to_vecs' not found on type 'dict'` — module-object member
  calls (`math.Vec3(...)`, module-level fn via module value) dispatch against
  the module dict in the interpreter.
- Root cause: same interpreter module-path-call gap already documented for
  actor_model (item 17). Fix lands in interpreter dispatch (forbidden path).

### math_autograd_runtime (item 20) — GATED (API does not exist + backend unwired)

- Failure (7/9 examples): `semantic: unknown static method from_data on class
  Tensor`.
- Root cause: spec imports `use std.torch.{Tensor}`
  (`src/lib/gc_async_mut/torch/mod.spl`), whose Tensor exposes only
  zeros/ones/randn/from_handle — no `from_data`, no autograd surface
  (requires_grad/grad/nograd). The API shape the spec wants exists only on the
  separate pure-autograd Tensor (`src/lib/gc_async_mut/pure/autograd.spl`, and
  with a different signature — mandatory `shape` arg). Even with `from_data`
  added, the rt_torch_* backend is the same unwired torch SFFI as item 22.
  Needs a deliberate API decision (wire std.torch autograd or retarget the
  spec at pure autograd) — out of sweep scope.

### allow_suppressions (item 29) — GATED (extern missing from deployed interpreter)

- Failure (1/5 examples, rest pass): `semantic: unknown extern function:
  rt_cli_dispatch_rust` on "AC-2: cli_dispatch_rust accepts named cmd args".
- Root cause: `rt_cli_dispatch_rust` is declared in
  `src/lib/nogc_sync_mut/sffi/cli.spl` and exported by the Rust runtime symbol
  table, but the deployed self-hosted interpreter binary does not register it.
  Fix is in the interpreter extern dispatch (forbidden path) and/or requires a
  bootstrap rebuild+redeploy (see memory: extern additions need bootstrap).

### llvm_parity (item 8) — GATED (native LLVM abort), call-site drift FIXED

- First failure layer (fixed): all 7 examples failed with `function expects
  argument for parameter 'opt_level_i64', but none was provided` — the spec
  still called `compile_module_with_backend(name, module, is_release)` with 3
  args after the signature grew a mandatory `opt_level_i64`. Spec call sites
  updated (release → 2/Speed, debug → 0/None_), kept in the file.
- Second failure layer (blocker): with correct calls, the run aborts with
  `LLVM ERROR: not a number, or does not fit in an unsigned int` and dumps
  core inside the native LLVM backend while compiling the spec's minimal MIR
  module. Process-killing engine crash in the llvm/llvm-lib lowering — needs
  backend root-causing, out of sweep scope. Tag restored.

### llvm_backend_spec (item 14) — FIXED (33/33, tags removed)

- Failure was a single stale expectation: `compatibility_build(X86_64)`
  returns `x86-64-v1` (the documented 2003+/no-AVX baseline in
  `src/compiler/70.backend/backend/llvm_target.spl`), while the spec still
  expected pre-baseline `x86-64`. `llvm_backend_tools.spl` normalizes
  v1 → `x86-64` only at the llc command line, so the config-level value is
  intentionally `x86-64-v1`. Expectation updated to the documented value —
  not a weakening. All 5 `only-compiled` context tags removed; 33 examples
  pass.

### app_mcp_intensive (item 15) — FIXED (35/35, all 7 tags removed)

Three independent spec bugs, all fixed at source in the spec:
- **Bare dict-literal keys** (`{ tool: "...", id: i, ... }`) are evaluated as
  variable-reference key expressions, producing `variable 'tool'/'id'/'name'/
  'jsonrpc'/'timestamp' not found`. Quoted all literal keys (matching the
  quoted-key dicts in the same file that already passed).
- **Exclusive-range off-by-ones**: `for i in 0..99` (etc.) yields N-1
  iterations vs the asserted N. Bumped all count-driving ranges
  (0..99→0..100, 0..49→0..50, 0..499→0..500, 0..199→0..200, 0..399→0..400,
  `0..(batches-1)`→`0..batches`). Also `queue[1..-1]` dropped first AND last
  element (50 processed vs 100) — replaced with `queue[1..queue.len()]`. The
  timeout example's `0..100` with `duration = i*10 > 5000` could never fire
  even inclusively — bumped to 0..1000 to make the assertion reachable.
- **Tool-set filtering**: the source-mode MCP server now defaults to the
  filtered "core" advertisement (2 tools), so `tools/list` lacked
  `debug_create_session`. The spec asserts full advertisement, so
  `_send_mcp_intensive` now pins `SIMPLE_MCP_TOOL_SET=all` (verified: full
  list includes debug_create_session with the env set).

### loader_exec_memory (item 16) — GATED (native exec-memory externs interpreter-null)

- Failure: first `assert_true(addr > 0)` — `native_alloc_exec_memory` returns
  0 under the interpreter (the oversized-allocation example passes only
  because it expects 0). The spec's own comment states these native exec
  memory functions require compiled mode. Interpreter/runtime gap; tag
  restored.

### Incident note 2 (2026-07-03, batch 2)

The same parallel-snapshot hazard recurred: hourly-sync commit `478a210fd9b`
swept this pass's temporarily-untagged batch-2 specs (items 20, 21, 22, 29)
into HEAD while they were under test. Tags were restored from `2db6c8ab13e`
and re-committed by this pass immediately after detection.

### Incident note (2026-07-03, task #76 pass)

While this pass had the four specs above temporarily untagged in the working
copy, a parallel session's snapshot swept the edits into its own commit
(`7e33394e202`, "fix(types): resolve ANY-erased field sites"), briefly leaving
the four failing specs untagged at HEAD. The tags were re-added and committed
by this pass immediately after detection.

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
