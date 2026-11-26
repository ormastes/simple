# Stage2 LLVM codegen blows up on large module-level array literals

- **ID:** stage2_codegen_large_array_literal_2026-11-02
- **Priority:** P1 (blocks phase-3 whole-program build)
- **Status:** ROOT-FIXED+STAGE2-GATED (`unicode_17_0_0.spl` remains text-encoded because frozen Stage 2 bootstrap compilers still OOM on large raw array literals; Stage 3 `MirToLlvm` root fix landed in WA-P2 2026-11-26).
- **Binary:** frozen stage2 `C:/dev/p3new/stage2.exe` built from `ef0681fc0e1`
- **Runs:** phase-3 runs 20b and 21 (dynload `--emit-archive`, 32 MIR shards)

## Symptom

Both runs were killed at the 97 GB cap at the same point: LLVM codegen of
`lib.common.search.generated.unicode_17_0_0`
(`src/lib/common/search/generated/unicode_17_0_0.spl`, 120 KB, generated).
The trace (`C:/dev/p3new/r11/build.log.err`) shows thousands of
`MIRB-AGG enter ... arm=array operands=316/928...` lines. Earlier modules
codegen in 2-27 s.

The module holds 17 module-level `[i64]` array literals, up to 3127 elements each
(about 25,000 elements in total). Stage2's array-aggregate MIR/LLVM lowering
grows superlinearly in memory with operand count.

## Workaround (this change)

`unicode_17_0_0.spl` now stores each table as a comma-separated `text` constant
(`_unicode_<name>_text`) and decodes it once through a memoized accessor
`_unicode_<name>() -> [i64]` (module `var` cache plus a ready flag). All tables were
private, so only internal call sites changed (`_unicode_x[i]` became `_unicode_x()[i]`).
The public API is unchanged. The module carries
`# @workaround bug=stage2_codegen_large_array_literal_2026-11-02`.

A spec hook `unicode_table_samples_for_spec()` returns `[len, first, mid, last]`
for each table. `test/01_unit/lib/common/search/unicode_17_0_0_text_tables_spec.spl`
compares those against the values taken from the original literals. The existing
`unicode_17_0_0_spec.spl` checks the every-scalar fingerprint and the full
NormalizationTest corpus.

## Follow-ups

1. **Generator:** `examples/05_stdlib/spipe/tools/unicode/generate_unicode_tables.mjs`
   must be updated to emit the text-table and accessor form. Until then,
   regenerating will bring the literals back. Also update
   `unicode_table_generator_sha256`.
2. **Compiler fix:** make array-aggregate lowering linear (emit a constant global
   initializer for all-constant `[i64]` literals instead of per-operand aggregate
   construction). After that, revert the workaround.
3. **Other large module-level literals in the stage3 closure** (by comma count;
   not changed here, re-check them if codegen stalls on these modules):
   - `src/lib/common/web/public_suffix_data.spl:11` `[text]` ~10.4k
   - `src/lib/gc_async_mut/gpu/browser_engine/html_named_character_references.spl:11,2245` `[text]` ~2.2k each
   - `src/app/cli/query_error_pattern_matcher.spl:24,100,176,252,328` `[u16]` ~1.16k each
   - `src/lib/common/image/webp_vp8_decode.spl:1244,1342,1440` `[i64]` ~0.9-1.05k
   - `src/compiler/15.blocks/blocks/unicode_classification_v17.spl` is 2 KB with no
     large literal, so it is not affected.

## Verification

Stage2 probe, 16 GB cap: `native-build --entry-closure --entry
src/lib/common/search/analyzer.spl --emit-object`. The results are in the PR description.

Result (2026-11-02, `measure.ps1 -CapGB 16`, 8 threads):
`first_obj_s=266.3 total_s=322.2 peak_tree_GB=3.86 objs=12 killed=False`.
The `unicode_17_0_0` object (`aot-a0ee9ab1...o`, 170 KB, its receipt names the
module) was written about 1-2 s after the previous object (the probe ran without
`SIMPLE_COMPILER_TRACE`, so it has no `MIRB-AGG` lines to compare). The final `-o` COFF relocatable merge fails with rc=1 because
ld.bfd is not installed. That failure is environmental, not codegen, and the
reference `C:/dev/p3new/cgprobe/common_api` probe hits it too.

Data parity: after stripping the declaration syntax, the 17 table bodies are
byte-identical to the original literal bodies (`cmp`). Apart from the `()`
accessor calls, the function bodies are unchanged. No table contains a negative
value. The decoder accepts only digits and commas.

The SPipe specs could not be run on this host. `bin/simple.exe` is the Rust seed
and fails to parse an unrelated file (`windows_redirected_process.spl`). Stage2
has no `test` command. A native driver executable built with the
`core-c-bootstrap` bundle failed to link (`rt_process_spawn_session` is
undefined), also environmental.

## WA-S8 Verification (2026-11-26)

- **Classification:** `KEPT-WITH-REASON`
- **Disposition:** Kept compact text-encoded tables and `@workaround bug=stage2_codegen_large_array_literal_2026-11-02` in `src/lib/common/search/generated/unicode_17_0_0.spl`. `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl` (`case Array(_):`) still emits `rt_array_new` plus per-element `rt_array_push` calls, and `unicode_17_0_0.spl` lies in the Stage 3 closure compiled by frozen Stage 2 binaries under the 97 GB RSS cap.
- **Verification (`SIMPLE_BINARY=wa_shared_bin/simple.exe`, build-commit `03a407dabae`, `--mode=interpreter`):**
  - `test/01_unit/lib/common/search/unicode_17_0_0_text_tables_spec.spl` (2/2 passed)
  - `test/01_unit/app/devhub/wa_src_lane8_retirement_spec.spl` (5/5 passed — exercises `unicode_table_samples_for_spec`, `unicode_is_alphabetic`, `unicode_canonical_combining_class`)
  - `test/01_unit/compiler/mir/wa_src_lane8_lowering_spec.spl` (4/4 passed — guards that `MirToLlvm` still emits `rt_array_push` per element for `Array` aggregates)

## WA-P2 Root Fix & Verification (2026-11-26)

- **Classification:** `ROOT-FIXED+STAGE2-GATED`
- **Root Fix (`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`, `src/compiler/70.backend/backend/llvm_ir_builder.spl`):**
  - When `AggregateKind.Array(_)` has `operands.len() >= 16` (`MIR_LLVM_CONST_ARRAY_LOOP_THRESHOLD`) and all elements are homogeneous compile-time `MirOperandKind.Const` values:
    - Scalar arrays (`Int`, `Bool`, `Float`, `FloatLexeme`, `Zero`, pointer-width integers) emit a module-level `private unnamed_addr constant [N x i64]` table with 8-byte `natural_alignment("i64")` and exact `store_field_bits_verbatim` bit parity plus an O(1)-IR `phi` induction loop calling `rt_array_new(N)` and `rt_array_push`.
    - String arrays (`Opaque("str")` boxed text or raw `ptr` literals) emit constant string globals plus `[N x ptr]` (target-width pointer alignment) and `[N x i64]` byte lengths (`align 8` for boxed text) and an O(1)-IR `phi` induction loop calling `rt_string_new_literal` + `rt_array_push` (or `ptrtoint` + `rt_array_push`).
  - Track active MIR block exit labels on `LlvmIRBuilder` (`current_mir_block_id`, `block_exit_labels`, `reset_mir_block_tracking`, `mir_block_exit_label`) across `emit_label("bb<id>")` and inline loop splits (`arr_done_*`), and resolve incoming blocks in `emit_ssa_phi_intrinsic` via `llvm_phi_incoming_block_label` so `__simple_ssa_phi` matches split-block predecessors.
  - Arrays with `< 16` elements or non-constant operands stay on the existing per-element `rt_array_push` path.
- **Stage 2 Bootstrap Gate:** Text-encoded memoized tables in `src/lib/common/search/generated/unicode_17_0_0.spl` (and `public_suffix_data.spl` / `html_named_character_references.spl`) remain untouched after upstream PR `#11846` (`307fc728ef9`) replaced their `@workaround` markers with `# Note:` comments, since frozen Stage 2 bootstrap compilers still compile those modules.
- **Verification (base `60948b5cc58`, `simple.exe --mode=interpreter`):**
  - `test/01_unit/compiler/backend/llvm_large_const_array_lowering_spec.spl` (9/9 passed, covering `<16`, `256`-element `[i64]`, bit parity, `[text]`, non-const & mixed-kind fallbacks, multi-array block labels, split-block `__simple_ssa_phi` diamond CFG + next-fn reset, and 32-bit `X86`/`Arm` alignment)
  - Real emitted `MirToLlvm` LLVM IR (64-bit diamond-split `__simple_ssa_phi` + `[text]`, and 32-bit `X86` `--target=i686-unknown-linux-gnu` diamond + `[i64]` + `[text]`) assembled cleanly with `clang.exe -c -x ir` (exit 0 on both)
  - `test/01_unit/compiler/backend/backend_capability_spec.spl` (21/21 passed)
  - `test/01_unit/lib/common/search/unicode_17_0_0_text_tables_spec.spl` (2/2 passed)
  - `test/01_unit/lib/gc_async_mut/gpu/browser_engine/large_literal_build_budget_spec.spl` (4/4 passed)
  - `test/01_unit/compiler/mir/wa_src_lane8_lowering_spec.spl` (4/4 passed)
  - `simple.exe lint --fast --jobs=1` on `llvm_ir_builder.spl`, `aggregate_intrinsics.spl`, and `llvm_large_const_array_lowering_spec.spl` (0 errors)
  - Static guards (`direct-env-runtime-guard.shs --working`, `check-keyword-identifier-bindings.shs`, `SRC_ADDED_NIL=0`, `doc/06_spec/*_spec.spl` == 0) all passed
  - 11 LLVM backend unit specs (`llvm_ir_builder_spec.spl`, `llvm_ir_builder_target_header_lifetime_spec.spl`, `llvm_aggregate_operand_at_contract_spec.spl`, `llvm_indexed_operand_by_value_spec.spl`, `llvm_aggregate_field_stale_ptr_local_spec.spl`, `llvm_emitter_ssa_violation_guard_spec.spl`, `llvm_const_value_total_match_guard_spec.spl`, `llvm_array_value_copy_single_ssa_def_spec.spl`, `llvm_bootstrap_string_cache_scope_spec.spl`, `llvm_pointer_integer_constant_spec.spl`, `llvm_runtime_decls_unique_spec.spl`) all passed
