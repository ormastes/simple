# Tautology-guarded skip specs: a repo-wide false-green family (2026-08-04)

**Status:** OPEN — 4 specs repaired and sabotage-proven; complete inventory below.

## Summary

A large family of specs replaces a real `it` body with a **tautology that cannot
fail**:

```
it "skipped":
    val pending_reason = "pre-existing test failures - functions/imports not available"
    expect(pending_reason.len()).to_be_greater_than(0)
```

`pending_reason` is bound to a **string literal** in every single instance
(747/747 occurrences of the `pending_reason` variant — zero exceptions), so
`.len() > 0` is a constant `true`. The runner prints a green `✓ skipped` and
`1 example, 0 failures`, exit 0. Verified verbatim:

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run test/01_unit/app/desugar/trait_scanner_spec.spl
Trait Scanner
  ✓ skipped

1 example, 0 failures
```

This is worse than a missing test: it inflates pass counts and hides that the
feature was never verified. The repo **already supports an honest form** —
`pending "name"` (`bdd.rs:782`) prints `○ name (skipped)` and records
`skipped=true`. Proof:

```
probe
  ✓ real pass
  ○ deferred thing (skipped)
  ✓ tautology

3 examples, 0 failures
```

## Census (each criterion counted separately)

Enumeration used `find` **without** `-L` plus `realpath` identity, so the 14
`test/` → `src/` directory symlinks (e.g. `test/01_unit/compiler/compiler ->
../../../src/compiler`, and `test/01_unit/lib/database/lib` which points at an
**absolute path in a different clone**) never aliased production files into the
walk. 19,139 spec paths, 19,139 distinct realpaths.

| Criterion | Files | Occurrences |
|---|---|---|
| (a) `it` title matching skip/pending/TODO/not-implemented | 1,339 | — |
| (b) commented-out `expect(` lines in the body | 345 | 8,612 |
| (a) ∧ (b) | 247 | — |
| (c-1) `expect(V.len()).to_be_greater_than(0)` where `V` is bound to a **string literal in the same `it`** | 720 | 881 |
| (c-1) restricted to the `pending_reason` name | 701 | 747 |
| (c-2) `expect(C).to_equal(C)` — same literal both sides | 349 | 1,365 |
| (c-3) `expect(true).to_be_true()` / `expect(false).to_be_false()` | 10 | 35 |
| bare `assert` (inert in this runner) | 12 | 134 |

The **union of (a) and (b) is not the vacuous set**. The vacuous set is (c).

### False-positive rate

- Loose regex `expect(*.len()).to_be_greater_than(0)` matches **1,051** files.
  Requiring the subject to be bound to a string literal in the same `it` block
  leaves **720**. Raw false-positive rate **31.5 %** (331/1,051).
- A naive "constant comparison" scan reports **4,867** occurrences. **3,601 of
  those (74.0 %) are `FAILMARK`s** — deliberate always-*false* assertions such as
  `expect(false).to_equal(true)` in an unreachable `case` arm, or
  `Err(e): expect("PRINT 2 failed: {e}").to_equal("")`. Those are correct code.
  Only the always-*true* 1,400 are vacuous.
- Path-shape false positive hit during this work: a regex `^use [a-z_.]*`
  captured the trailing `.` of `use compiler.core.lexer.{...}`, so 6/13 module
  lookups resolved to nothing — the same defect that once invented 1,105 phantom
  import sites.

### Duplicate trees

`test/unit` and `test/01_unit` are **separate file copies**, not symlinks: of the
701 `pending_reason` files, 243 exist in both trees (236 byte-identical, 7
divergent), 202 exist only in `test/unit`, 1 only in `test/01_unit`. 701 paths →
419 distinct file contents. Repairs here were applied to **both** copies when
they were byte-identical beforehand.

### Ground-truth validation

The census independently rediscovers the four seed specs and the
`ExhaustivenessCheck` guard: `ExhaustivenessCheck` is declared at
`src/compiler/95.interp/interpreter/pattern.spl:65` and re-exported through
`src/compiler/35.semantics/pattern_analysis.spl`; its spec
`test/01_unit/lib/common/pattern_analysis_spec.spl` is in the (c-1) set. All
four seed specs appear in the inventory below.

## Triage

94 canonical-tree specs were mechanically restored (strip the stub block,
un-comment the body) and executed. Outcomes:

| Class | Files | Examples | Failures |
|---|---|---|---|
| (i) restores fully green | 17 | 241 | 0 |
| (ii) restores mixed — real defects exposed | 25 | 841 | 398 |
| (ii) restores all-red | 8 | 261 | 261 |
| (iii) will not load (stale module/API paths) | 44 | 0 | — |

**But a green restore is not automatically a repair.** Screening the 17 class-(i)
files found two further vacuity variants:

- `test/01_unit/compiler/semantics/safety_checker_spec.spl` — 26 examples, zero
  production imports; every assertion is `check(code.contains("asm"))` against
  the test's own string literal. Restoring it would have swapped 1 false green
  for 26.
- `test/01_unit/app/devtools/devtools_cli_spec.spl` — 9 × `check(true)`.

A **coupling gate** (rename every top-level `fn` in the imported module; require
the spec's example count to drop or its failure count to rise) then cleared only
4 of the remaining 13. The other 9 restore green but their coupling to
production code is unproven — they are **not** landed.

## Repaired (sabotage-proven)

| Spec | before | after |
|---|---|---|
| `test/01_unit/compiler/backend/macho_writer_spec.spl` (+ `test/unit/…`) | `1 example, 0 failures` (tautology) | `39 examples, 0 failures` |
| `test/01_unit/compiler_core/lexer_spec.spl` (+ `test/unit/…`) | `1 example, 0 failures` | `8 examples, 0 failures` |
| `test/01_unit/compiler/mir/collection_opt_spec.spl` (+ `test/unit/…`) | `1 example, 0 failures` | `5 examples, 0 failures` |
| `test/01_unit/compiler/semantics/collection_patterns_lint_spec.spl` (+ `test/unit/…`) | `1 example, 0 failures` | `11 examples, 0 failures` |

Sabotage proof (behavioural, `macho_writer`): changing
`CPU_TYPE_ARM64 = 0x0100000c` → `0x0100000d` in
`src/compiler/70.backend/backend/native/macho_writer.spl` turns
`39 examples, 0 failures` into `39 examples, 2 failures` naming
`✗ has correct CPU type for ARM64` and `✗ has correct CPU_TYPE_ARM64 value`;
reverting returns `39 examples, 0 failures`.

Coupling proof for the other three: renaming every top-level `fn` in the imported
module drives them to `8/8`, `5/5` and `11/11` failures respectively; reverting
returns them to 0.

Net effect: **4 vacuous examples removed, 63 genuine assertions activated**
(×2 for the mirrored `test/unit` copies). No previously-green number went red in
this change.

## Defects found while restoring (not yet filed separately)

Restoring `test/01_unit/compiler_core/ast_spec.spl` (stated reason: *"imports
compiler modules - causes OOM via numbered directory resolution"* — **false**, it
runs in seconds) yields `11 examples, 3 failures`:

1. `expr_get_args(<array literal>).len()` → `1`, expected `2`.
2. `expr_get_extra(<range>)` → `-1`, expected `1`.
3. `expr_func_decl` — *"function expects argument for parameter `type_params`,
   but none was provided"* (spec and implementation disagree on arity).

## Measurement traps hit during this work

- **The runner prints one `N examples, M failures` line per `describe` block**,
  not one per file. Grepping `tail -1` reported `3 examples, 0 failures` for a
  file whose real total was `21 of 39 example(s) failed`. Sum every summary line,
  or read the trailing `spec failure: X of Y example(s) failed`.
- **A module-load failure silently DROPS whole `describe` blocks** with exit 0
  and `0 failures`: renaming `scan_traits` in
  `src/app/desugar/trait_scanner.spl` took
  `test/01_unit/app/desugar/trait_scanner_spec.spl` from 9 examples to 3, still
  reporting green. A coupling gate keyed on *failures* is therefore fail-open; it
  must also compare **example counts**.
- `check(cond)` is a real assertion (`check(1 == 2)` fails), so `check(true)` and
  `check(<literal>.contains(...))` are vacuity variants that a scan for
  `expect(` misses entirely.

## Remaining inventory

Complete list of the 720 files carrying the literal-bound `.len() > 0` tautology,
with occurrence counts. The 4 repaired above are excluded.

| Spec | tautologies |
|---|---|
| test/03_system/feature/usage/static_const_declarations_spec.spl | 53 |
| test/03_system/feature/usage/alias_deprecated_spec.spl | 42 |
| test/integration/doctest/discovery_spec.spl | 11 |
| test/02_integration/doctest/discovery_spec.spl | 11 |
| test/integration/compiler/llvm_parity_spec.spl | 9 |
| test/02_integration/compiler/llvm_parity_spec.spl | 9 |
| test/integration/compiler/llvm_compiled_proof_spec.spl | 6 |
| test/02_integration/compiler/llvm_compiled_proof_spec.spl | 6 |
| test/system/web_app_packaging_spec.spl | 2 |
| test/03_system/infrastructure/web_app_packaging_spec.spl | 2 |
| test/unit/tools/shell/test_spec.spl | 1 |
| test/unit/std/mock_spec.spl | 1 |
| test/unit/std/hooks/hook_registry_spec.spl | 1 |
| test/unit/std/feature_validation/testing_framework_spec.spl | 1 |
| test/unit/std/exp/sweep_spec.spl | 1 |
| test/unit/std/exp/storage_spec.spl | 1 |
| test/unit/std/exp/run_spec.spl | 1 |
| test/unit/std/exp/config_spec.spl | 1 |
| test/unit/std/exp/artifact_spec.spl | 1 |
| test/unit/std/context_spec.spl | 1 |
| test/unit/std/condition_spec.spl | 1 |
| test/unit/memleak/c_runtime_leak_spec.spl | 1 |
| test/unit/lib/torch_spec.spl | 1 |
| test/unit/lib/sanitizer/sanitizer_spec.spl | 1 |
| test/unit/lib/qemu_spec.spl | 1 |
| test/unit/lib/pure/utils_spec.spl | 1 |
| test/unit/lib/pure/training_spec.spl | 1 |
| test/unit/lib/pure/training_extended_spec.spl | 1 |
| test/unit/lib/pure/tensor_spec.spl | 1 |
| test/unit/lib/pure/tensor_ops_spec.spl | 1 |
| test/unit/lib/pure/tensor_f64_ops_extended_spec.spl | 1 |
| test/unit/lib/pure/tensor_advanced_spec.spl | 1 |
| test/unit/lib/pure_parser_phase1_spec.spl | 1 |
| test/unit/lib/pure_parser_phase1_2_spec.spl | 1 |
| test/unit/lib/pure_parser_load_spec.spl | 1 |
| test/unit/lib/pure/optim/scheduler_spec.spl | 1 |
| test/unit/lib/pure/nn_spec.spl | 1 |
| test/unit/lib/pure/nn/serialization_spec.spl | 1 |
| test/unit/lib/pure/nn/pooling_spec.spl | 1 |
| test/unit/lib/pure/nn/pooling_integration_spec.spl | 1 |
| test/unit/lib/pure/nn/norm_spec.spl | 1 |
| test/unit/lib/pure/nn/loss_spec.spl | 1 |
| test/unit/lib/pure/nn/init_spec.spl | 1 |
| test/unit/lib/pure/nn/functional_spec.spl | 1 |
| test/unit/lib/pure/nn_extended_spec.spl | 1 |
| test/unit/lib/pure/nn/embedding_spec.spl | 1 |
| test/unit/lib/pure/nn/embedding_integration_spec.spl | 1 |
| test/unit/lib/pure/nn/embedding_backward_spec.spl | 1 |
| test/unit/lib/pure/nn/conv_spec.spl | 1 |
| test/unit/lib/pure/nn/conv_integration_spec.spl | 1 |
| test/unit/lib/pure/nn/attention_spec.spl | 1 |
| test/unit/lib/pure/metrics_spec.spl | 1 |
| test/unit/lib/pure/data_spec.spl | 1 |
| test/unit/lib/pure/data_loader_spec.spl | 1 |
| test/unit/lib/pure/autograd_spec.spl | 1 |
| test/unit/lib/pure/autograd_extended_spec.spl | 1 |
| test/unit/lib/pure/autograd_advanced_spec.spl | 1 |
| test/unit/lib/ptr/ptr_spec.spl | 1 |
| test/unit/lib/physics/vector_spec.spl | 1 |
| test/unit/lib/physics/spatial_hash_spec.spl | 1 |
| test/unit/lib/physics/shapes_spec.spl | 1 |
| test/unit/lib/physics/rigidbody_spec.spl | 1 |
| test/unit/lib/physics/materials_spec.spl | 1 |
| test/unit/lib/physics/contact_spec.spl | 1 |
| test/unit/lib/physics/aabb_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/thread_sffi_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/thread_safe_queue_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/thread_pool_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/qemu_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/collections/ring_buffer_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/collections/fixed_stack_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/async/scheduler_spec.spl | 1 |
| test/unit/lib/nogc_async_mut_noalloc/async/poll_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/test_ffi_operator_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/simple_math_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/pure_load_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/fft_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/data_pipeline_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/custom_autograd_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/async_training_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/ml/activation_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/mailbox_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/io/event_loop_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/gen_statem_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/gen_server_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/gen_event_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/generator_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/game3d/physics_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/game3d/material_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/game3d/input_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/game3d/assets_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/async_host_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/async_host_mt_spec.spl | 1 |
| test/unit/lib/nogc_async_mut/async_embedded_spec.spl | 1 |
| test/unit/lib/ml/test_ffi_operator_spec.spl | 1 |
| test/unit/lib/ml/simple_math_spec.spl | 1 |
| test/unit/lib/ml/fft_spec.spl | 1 |
| test/unit/lib/ml/custom_autograd_spec.spl | 1 |
| test/unit/lib/ml/activation_spec.spl | 1 |
| test/unit/lib/lms/server_spec.spl | 1 |
| test/unit/lib/i18n/resource_bundle_spec.spl | 1 |
| test/unit/lib/gc_async_mut/dl/config_spec.spl | 1 |
| test/unit/lib/gc_async_mut/dl/config_loader_spec.spl | 1 |
| test/unit/lib/diagnostics/text_formatter_spec.spl | 1 |
| test/unit/lib/diagnostics/simple_formatter_spec.spl | 1 |
| test/unit/lib/diagnostics/json_formatter_spec.spl | 1 |
| test/unit/lib/diagnostics/i18n_context_spec.spl | 1 |
| test/unit/lib/database/feature_utils_extract_spec.spl | 1 |
| test/unit/lib/database/database_test_extended_spec.spl | 1 |
| test/unit/lib/database/database_feature_spec.spl | 1 |
| test/unit/lib/database/database_e2e_spec.spl | 1 |
| test/unit/lib/database/database_atomic_spec.spl | 1 |
| test/unit/lib/database/core_interner_table_spec.spl | 1 |
| test/unit/lib/common/unicode_math_spec.spl | 1 |
| test/unit/lib/common/traits_wired_spec.spl | 1 |
| test/unit/lib/common/traits_spec.spl | 1 |
| test/unit/lib/common/tap_spec.spl | 1 |
| test/unit/lib/common/string_core_spec.spl | 1 |
| test/unit/lib/common/string_compiled_spec.spl | 1 |
| test/unit/lib/common/.sspec_wrapped_entry_error_format_spec.spl | 1 |
| test/unit/lib/common/set_utils_operations_spec.spl | 1 |
| test/unit/lib/common/seq_ce_spec.spl | 1 |
| test/unit/lib/common/seq_ce_e2e_spec.spl | 1 |
| test/unit/lib/common/repr_spec.spl | 1 |
| test/unit/lib/common/pure/utils_spec.spl | 1 |
| test/unit/lib/common/pure/training_spec.spl | 1 |
| test/unit/lib/common/pure/training_extended_spec.spl | 1 |
| test/unit/lib/common/pure/tensor_spec.spl | 1 |
| test/unit/lib/common/pure/tensor_ops_spec.spl | 1 |
| test/unit/lib/common/pure/tensor_f64_ops_extended_spec.spl | 1 |
| test/unit/lib/common/pure/tensor_advanced_spec.spl | 1 |
| test/unit/lib/common/pure/pure_parser_phase1_spec.spl | 1 |
| test/unit/lib/common/pure/pure_parser_phase1_2_spec.spl | 1 |
| test/unit/lib/common/pure/pure_parser_load_spec.spl | 1 |
| test/unit/lib/common/pure/optim/scheduler_spec.spl | 1 |
| test/unit/lib/common/pure/nn_spec.spl | 1 |
| test/unit/lib/common/pure/nn/serialization_spec.spl | 1 |
| test/unit/lib/common/pure/nn/pooling_spec.spl | 1 |
| test/unit/lib/common/pure/nn/pooling_integration_spec.spl | 1 |
| test/unit/lib/common/pure/nn/norm_spec.spl | 1 |
| test/unit/lib/common/pure/nn/loss_spec.spl | 1 |
| test/unit/lib/common/pure/nn/init_spec.spl | 1 |
| test/unit/lib/common/pure/nn/functional_spec.spl | 1 |
| test/unit/lib/common/pure/nn_extended_spec.spl | 1 |
| test/unit/lib/common/pure/nn/embedding_spec.spl | 1 |
| test/unit/lib/common/pure/nn/embedding_integration_spec.spl | 1 |
| test/unit/lib/common/pure/nn/embedding_backward_spec.spl | 1 |
| test/unit/lib/common/pure/nn/conv_spec.spl | 1 |
| test/unit/lib/common/pure/nn/conv_integration_spec.spl | 1 |
| test/unit/lib/common/pure/nn/attention_spec.spl | 1 |
| test/unit/lib/common/pure/metrics_spec.spl | 1 |
| test/unit/lib/common/pure/data_spec.spl | 1 |
| test/unit/lib/common/pure/data_loader_spec.spl | 1 |
| test/unit/lib/common/pure/autograd_spec.spl | 1 |
| test/unit/lib/common/pure/autograd_extended_spec.spl | 1 |
| test/unit/lib/common/pure/autograd_advanced_spec.spl | 1 |
| test/unit/lib/common/phantom_spec.spl | 1 |
| test/unit/lib/common/newline_constants_spec.spl | 1 |
| test/unit/lib/common/mock_spec.spl | 1 |
| test/unit/lib/common/math_repr_spec.spl | 1 |
| test/unit/lib/common/math_repr_error_spec.spl | 1 |
| test/unit/lib/common/mathjax_spec.spl | 1 |
| test/unit/lib/common/iterable_spec.spl | 1 |
| test/unit/lib/common/hooks/hook_registry_spec.spl | 1 |
| test/unit/lib/common/helpers_spec.spl | 1 |
| test/unit/lib/common/fuzz_spec.spl | 1 |
| test/unit/lib/common/feature_validation/testing_framework_spec.spl | 1 |
| test/unit/lib/common/exp/sweep_spec.spl | 1 |
| test/unit/lib/common/exp/storage_spec.spl | 1 |
| test/unit/lib/common/exp/run_spec.spl | 1 |
| test/unit/lib/common/exp/config_spec.spl | 1 |
| test/unit/lib/common/exp/artifact_spec.spl | 1 |
| test/unit/lib/common/error_trace_spec.spl | 1 |
| test/unit/lib/common/error_spec.spl | 1 |
| test/unit/lib/common/error_format_spec.spl | 1 |
| test/unit/lib/common/error_core_spec.spl | 1 |
| test/unit/lib/common/diagnostics/text_formatter_spec.spl | 1 |
| test/unit/lib/common/diagnostics/simple_formatter_spec.spl | 1 |
| test/unit/lib/common/diagnostics/json_formatter_spec.spl | 1 |
| test/unit/lib/common/diagnostics/i18n_context_spec.spl | 1 |
| test/unit/lib/common/context_spec.spl | 1 |
| test/unit/lib/common/condition_spec.spl | 1 |
| test/unit/lib/common/color_utils_rgb_hsl_spec.spl | 1 |
| test/unit/compiler/type/runtime_type_check_spec.spl | 1 |
| test/unit/compiler/type_inference/variance_inference_spec.spl | 1 |
| test/unit/compiler/type_inference/type_infer_comprehensive_spec.spl | 1 |
| test/unit/compiler/type_inference/dim_constraints_spec.spl | 1 |
| test/unit/compiler/type_inference/bidir_type_check_spec.spl | 1 |
| test/unit/compiler/type_checker/type_inference_executable_spec.spl | 1 |
| test/unit/compiler/traits/associated_types_trait_spec.spl | 1 |
| test/unit/compiler_shared/diagnostics/span_spec.spl | 1 |
| test/unit/compiler_shared/diagnostics/severity_spec.spl | 1 |
| test/unit/compiler_shared/diagnostics/label_spec.spl | 1 |
| test/unit/compiler_shared/diagnostics/diagnostic_spec.spl | 1 |
| test/unit/compiler/semantics/safety_checker_spec.spl | 1 |
| test/unit/compiler/semantics/resolve_spec.spl | 1 |
| test/unit/compiler/semantics/effect_inference_spec.spl | 1 |
| test/unit/compiler/semantics/comptime_spec.spl | 1 |
| test/unit/compiler/semantics/closure_capture_warning_spec.spl | 1 |
| test/unit/compiler/semantics/call_graph_spec.spl | 1 |
| test/unit/compiler/semantics/borrow_check_spec.spl | 1 |
| test/unit/compiler/semantics/arch_rules_syntax_spec.spl | 1 |
| test/unit/compiler/semantics/alloc_inference_spec.spl | 1 |
| test/unit/compiler/semantics/alloc_checker_spec.spl | 1 |
| test/unit/compiler/parser/struct_update_spec.spl | 1 |
| test/unit/compiler/parser/parser_step_spec.spl | 1 |
| test/unit/compiler/parser/parser_outline_spec.spl | 1 |
| test/unit/compiler/parser/parser_new_spec.spl | 1 |
| test/unit/compiler/parser/parser_factory_spec.spl | 1 |
| test/unit/compiler/parser/parse_formats_spec.spl | 1 |
| test/unit/compiler/parser/parse_error_spec.spl | 1 |
| test/unit/compiler/parser/lexer_contextual_keywords_spec.spl | 1 |
| test/unit/compiler/parser/grammar_compile_spec.spl | 1 |
| test/unit/compiler/parser/dyn_trait_spec.spl | 1 |
| test/unit/compiler/parser/do_block_spec.spl | 1 |
| test/unit/compiler/parser/defer_spec.spl | 1 |
| test/unit/compiler/parser/ast_debug_spec.spl | 1 |
| test/unit/compiler/native/x86_64_simd_spec.spl | 1 |
| test/unit/compiler/native/native_compile_spec.spl | 1 |
| test/unit/compiler/native/cli_interpreter_path_spec.spl | 1 |
| test/unit/compiler/native/auto_vectorize_spec.spl | 1 |
| test/unit/compiler/native/arm_neon_spec.spl | 1 |
| test/unit/compiler/mono/note_sdn_spec.spl | 1 |
| test/unit/compiler/mono/note_sdn_bdd_spec.spl | 1 |
| test/unit/compiler/mono/monomorphize_spec.spl | 1 |
| test/unit/compiler/mono/mono_cache_efficiency_spec.spl | 1 |
| test/unit/compiler/mir/mir_serialization_spec.spl | 1 |
| test/unit/compiler/mir/mir_opt_spec.spl | 1 |
| test/unit/compiler/mir/mir_lowering_new_spec.spl | 1 |
| test/unit/compiler/mir/mir_enum_access_spec.spl | 1 |
| test/unit/compiler/mir/mir_data_spec.spl | 1 |
| test/unit/compiler/mdsoc/vc_static_spec.spl | 1 |
| test/unit/compiler/mdsoc/vc_import_spec.spl | 1 |
| test/unit/compiler/mdsoc/doc_validation_spec.spl | 1 |
| test/unit/compiler/mdsoc/cross_query_spec.spl | 1 |
| test/unit/compiler/mdsoc/construct_types_spec.spl | 1 |
| test/unit/compiler/mdsoc/construct_checker_spec.spl | 1 |
| test/unit/compiler/mdsoc/config_multi_dim_spec.spl | 1 |
| test/unit/compiler/macros/macro_integration_spec.spl | 1 |
| test/unit/compiler/linker/swa_zip_spec.spl | 1 |
| test/unit/compiler/lexer/source_position_spec.spl | 1 |
| test/unit/compiler/lexer/lexer_spec.spl | 1 |
| test/unit/compiler/lexer/lexer_new_spec.spl | 1 |
| test/unit/compiler/lexer/lexer_minimal_test_spec.spl | 1 |
| test/unit/compiler/lexer/lexer_import_debug_spec.spl | 1 |
| test/unit/compiler/lexer/lexer_comprehensive_spec.spl | 1 |
| test/unit/compiler/hir/hir_new_spec.spl | 1 |
| test/unit/compiler/hir/hir_lowering_spec.spl | 1 |
| test/unit/compiler/hir/hir_async_spec.spl | 1 |
| test/unit/compiler/hir/hir_async_integration_spec.spl | 1 |
| test/unit/compiler/hir/hir_async_errors_spec.spl | 1 |
| test/unit/compiler/driver/pipeline_var_spec.spl | 1 |
| test/unit/compiler/driver/pipeline_mir_spec.spl | 1 |
| test/unit/compiler/driver/pipeline_basic_spec.spl | 1 |
| test/unit/compiler/driver/driver_spec.spl | 1 |
| test/unit/compiler/driver/compiler_shared_di_check_spec.spl | 1 |
| test/unit/compiler/di/di_validation_spec.spl | 1 |
| test/unit/compiler/di/di_runtime_spec.spl | 1 |
| test/unit/compiler/di/di_proxy_spec.spl | 1 |
| test/unit/compiler/di/di_config_spec.spl | 1 |
| test/unit/compiler/dependency/visibility_spec.spl | 1 |
| test/unit/compiler/dependency/visibility_integration_spec.spl | 1 |
| test/unit/compiler/dependency/symbol_spec.spl | 1 |
| test/unit/compiler/dependency/resolution_spec.spl | 1 |
| test/unit/compiler/dependency/macro_import_theorems_spec.spl | 1 |
| test/unit/compiler/dependency/integration_spec.spl | 1 |
| test/unit/compiler/dependency/import_resolution_spec.spl | 1 |
| test/unit/compiler/dependency/graph_transitive_spec.spl | 1 |
| test/unit/compiler/dependency/graph_topo_spec.spl | 1 |
| test/unit/compiler/dependency/graph_cycles_spec.spl | 1 |
| test/unit/compiler/dependency/graph_basic_spec.spl | 1 |
| test/unit/compiler_core/type_subst_spec.spl | 1 |
| test/unit/compiler_core/types_spec.spl | 1 |
| test/unit/compiler_core/traits_spec.spl | 1 |
| test/unit/compiler_core/traits_module_spec.spl | 1 |
| test/unit/compiler_core/traits_extended_spec.spl | 1 |
| test/unit/compiler_core/traits_compiles_spec.spl | 1 |
| test/unit/compiler_core/tokens_spec.spl | 1 |
| test/unit/compiler_core/tmp_test_spec.spl | 1 |
| test/unit/compiler_core/structural_subtyping_spec.spl | 1 |
| test/unit/compiler_core/receive_spec.spl | 1 |
| test/unit/compiler_core/preprocess_conditionals_spec.spl | 1 |
| test/unit/compiler_core/pragma_msg_spec.spl | 1 |
| test/unit/compiler_core/parser_spec.spl | 1 |
| test/unit/compiler_core/parser_option_coverage_spec.spl | 1 |
| test/unit/compiler_core/parser_intensive_spec.spl | 1 |
| test/unit/compiler_core/new_tokens_spec.spl | 1 |
| test/unit/compiler_core/must_use_spec.spl | 1 |
| test/unit/compiler_core/mixin_expr_spec.spl | 1 |
| test/unit/compiler_core/mir_spec.spl | 1 |
| test/unit/compiler_core/lexer_intensive_spec.spl | 1 |
| test/unit/compiler_core/lang_basics_spec.spl | 1 |
| test/unit/compiler_core/keyof_token_spec.spl | 1 |
| test/unit/compiler_core/keyof_spec.spl | 1 |
| test/unit/compiler_core/interpreter/value_spec.spl | 1 |
| test/unit/compiler_core/interpreter/ops_spec.spl | 1 |
| test/unit/compiler_core/interpreter/jit_spec.spl | 1 |
| test/unit/compiler_core/interpreter/intensive_spec.spl | 1 |
| test/unit/compiler_core/interpreter/eval_spec.spl | 1 |
| test/unit/compiler_core/interpreter/env_spec.spl | 1 |
| test/unit/compiler_core/ignored_return_warning_spec.spl | 1 |
| test/unit/compiler_core/generic_syntax_spec.spl | 1 |
| test/unit/compiler_core/file_class_introspection_spec.spl | 1 |
| test/unit/compiler_core/exhaustiveness_spec.spl | 1 |
| test/unit/compiler_core/entity/entity_structure_spec.spl | 1 |
| test/unit/compiler_core/entity/entity_span_spec.spl | 1 |
| test/unit/compiler_core/eager_yield_spec.spl | 1 |
| test/unit/compiler_core/ce_block_spec.spl | 1 |
| test/unit/compiler_core/branch_coverage_36_spec.spl | 1 |
| test/unit/compiler_core/branch_coverage_33_spec.spl | 1 |
| test/unit/compiler_core/branch_coverage_31_spec.spl | 1 |
| test/unit/compiler_core/bind_stmt_spec.spl | 1 |
| test/unit/compiler_core/bidir_type_check_spec.spl | 1 |
| test/unit/compiler_core/ast_spec.spl | 1 |
| test/unit/compiler_core/ast_clone_spec.spl | 1 |
| test/unit/compiler_core/annotation_intrinsics_spec.spl | 1 |
| test/unit/compiler/config/literal_config_spec.spl | 1 |
| test/unit/compiler/config/error_formatter_spec.spl | 1 |
| test/unit/compiler/blocks/utils_spec.spl | 1 |
| test/unit/compiler/blocks/pre_lex_per_dsl_spec.spl | 1 |
| test/unit/compiler/blocks/pre_lex_info_spec.spl | 1 |
| test/unit/compiler/blocks/easy_api_spec.spl | 1 |
| test/unit/compiler/blocks/builder_api_spec.spl | 1 |
| test/unit/compiler/blocks/block_skip_policy_spec.spl | 1 |
| test/unit/compiler/blocks/block_outline_info_spec.spl | 1 |
| test/unit/compiler/blocks/block_definition_three_level_spec.spl | 1 |
| test/unit/compiler/backend/native_backend_spec.spl | 1 |
| test/unit/compiler/backend/llvm_wasm_spec.spl | 1 |
| test/unit/compiler/backend/llvm_lib_backend_spec.spl | 1 |
| test/unit/compiler/backend/instruction_coverage_spec.spl | 1 |
| test/unit/compiler/backend/expression_evaluator_spec.spl | 1 |
| test/unit/compiler/backend/execution_manager_spec.spl | 1 |
| test/unit/compiler/backend/differential_testing_spec.spl | 1 |
| test/unit/compiler/backend/differential_backend_consistency_spec.spl | 1 |
| test/unit/compiler/backend/backend_orchestration_spec.spl | 1 |
| test/unit/compiler/backend/backend_factory_spec.spl | 1 |
| test/unit/compiler/async/suspension_analysis_spec.spl | 1 |
| test/unit/compiler/async/state_enum_spec.spl | 1 |
| test/unit/compiler/async/poll_generator_spec.spl | 1 |
| test/unit/compiler/async/async_state_machine_spec.spl | 1 |
| test/unit/compiler/async/async_pipeline_spec.spl | 1 |
| test/unit/compiler/async/async_mir_spec.spl | 1 |
| test/unit/compiler/async/async_frame_analysis_spec.spl | 1 |
| test/unit/compiler/async/async_desugar_integration_spec.spl | 1 |
| test/unit/bugs/export_as_runtime_bug_spec.spl | 1 |
| test/unit/app/tooling/test_stats_spec.spl | 1 |
| test/unit/app/tooling/test_db_edge_cases_spec.spl | 1 |
| test/unit/app/tooling/symbol_hash_spec.spl | 1 |
| test/unit/app/tooling/coverage_threshold_spec.spl | 1 |
| test/unit/app/tooling/coverage_ffi_spec.spl | 1 |
| test/unit/app/tooling/context_pack_spec.spl | 1 |
| test/unit/app/tooling/color_utils_spec.spl | 1 |
| test/unit/app/tooling/brief_view_spec.spl | 1 |
| test/unit/app/spl_coverage_spec.spl | 1 |
| test/unit/app/semihost/reader_spec.spl | 1 |
| test/unit/app/project_cli_spec.spl | 1 |
| test/unit/app/package/semver_spec.spl | 1 |
| test/unit/app/package/semver_mini_spec.spl | 1 |
| test/unit/app/package/package_spec.spl | 1 |
| test/unit/app/package/manifest_spec.spl | 1 |
| test/unit/app/package/lockfile_spec.spl | 1 |
| test/unit/app/package/ffi_spec.spl | 1 |
| test/unit/app/package_cli_spec.spl | 1 |
| test/unit/app/mcp_unit/transport_edge_cases_spec.spl | 1 |
| test/unit/app/mcp_unit/simple_mcp_malformed_spec.spl | 1 |
| test/unit/app/mcp_unit/session_spec.spl | 1 |
| test/unit/app/mcp_unit/session_extended_spec.spl | 1 |
| test/unit/app/mcp_unit/resources_spec.spl | 1 |
| test/unit/app/mcp_unit/prompts_compiled_spec.spl | 1 |
| test/unit/app/mcp_unit/outline_renderer_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_tools_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_tasks_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_subscriptions_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_structured_output_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_server_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_sampling_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_jj_commit_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_dx_helpers_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_debug_tools_spec.spl | 1 |
| test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl | 1 |
| test/unit/app/mcp_unit/logging_basics_spec.spl | 1 |
| test/unit/app/mcp_unit/fileio_temp_spec.spl | 1 |
| test/unit/app/mcp_unit/fileio_lite_safe_read_spec.spl | 1 |
| test/unit/app/mcp_unit/failure_analysis_spec.spl | 1 |
| test/unit/app/mcp_unit/editor_spec.spl | 1 |
| test/unit/app/mcp_unit/di_integration_spec.spl | 1 |
| test/unit/app/mcp_unit/capabilities_spec.spl | 1 |
| test/unit/app/lsp/server_query_integration_spec.spl | 1 |
| test/unit/app/lsp/server_lifecycle_spec.spl | 1 |
| test/unit/app/lsp/references_spec.spl | 1 |
| test/unit/app/lsp/message_dispatcher_spec.spl | 1 |
| test/unit/app/lsp/hover_spec.spl | 1 |
| test/unit/app/lsp/hover_handler_spec.spl | 1 |
| test/unit/app/lsp/folding_range_spec.spl | 1 |
| test/unit/app/lsp/document_sync_spec.spl | 1 |
| test/unit/app/lsp/compiler_query_api_spec.spl | 1 |
| test/unit/app/lms/server_spec.spl | 1 |
| test/unit/app/leak_check/types_spec.spl | 1 |
| test/unit/app/io/window_ffi_spec.spl | 1 |
| test/unit/app/io/regex_sffi_spec.spl | 1 |
| test/unit/app/io/rapier2d_ffi_spec.spl | 1 |
| test/unit/app/io/process_limits_basic_spec.spl | 1 |
| test/unit/app/io/jit_availability_spec.spl | 1 |
| test/unit/app/io/http_ffi_spec.spl | 1 |
| test/unit/app/io/graphics2d_ffi_spec.spl | 1 |
| test/unit/app/io/gamepad_ffi_spec.spl | 1 |
| test/unit/app/io/file_shell_exec_spec.spl | 1 |
| test/unit/app/io/file_ops_rw_spec.spl | 1 |
| test/unit/app/io/dir_ops_create_list_spec.spl | 1 |
| test/unit/app/io/cli_ops_handlers_spec.spl | 1 |
| test/unit/app/io/audio_ffi_spec.spl | 1 |
| test/unit/app/interpreter/symbol_spec.spl | 1 |
| test/unit/app/interpreter/persistent_vec_spec.spl | 1 |
| test/unit/app/interpreter/persistent_dict_spec.spl | 1 |
| test/unit/app/interpreter/message_transfer_spec.spl | 1 |
| test/unit/app/interpreter/mailbox_spec.spl | 1 |
| test/unit/app/interpreter/lazy_val_spec.spl | 1 |
| test/unit/app/interpreter/lazy_seq_spec.spl | 1 |
| test/unit/app/interpreter/debug_spec.spl | 1 |
| test/unit/app/interpreter/class_method_call_spec.spl | 1 |
| test/unit/app/interpreter/actor_scheduler_spec.spl | 1 |
| test/unit/app/grammar_doc/doc_generator_spec.spl | 1 |
| test/unit/app/formatter_spec.spl | 1 |
| test/unit/app/formatter/formatter_spec.spl | 1 |
| test/unit/app/formatter/formatter_comprehensive_spec.spl | 1 |
| test/unit/app/formatter/formatter_basic_spec.spl | 1 |
| test/unit/app/formatter_comprehensive_spec.spl | 1 |
| test/unit/app/ffi_gen/module_gen_spec.spl | 1 |
| test/unit/app/doc/public_check/warnings_spec.spl | 1 |
| test/unit/app/doc/public_check/statistics_spec.spl | 1 |
| test/unit/app/diagram/filter_spec.spl | 1 |
| test/unit/app/diagram/diagram_gen_spec.spl | 1 |
| test/unit/app/diagram/call_flow_profiling_spec.spl | 1 |
| test/unit/app/devtools/devtools_cli_spec.spl | 1 |
| test/unit/app/desugar/trait_static_dispatch_spec.spl | 1 |
| test/unit/app/desugar/trait_scanner_spec.spl | 1 |
| test/unit/app/desugar/trait_desugar_spec.spl | 1 |
| test/unit/app/desugar/struct_defaults_spec.spl | 1 |
| test/unit/app/desugar/static_methods_desugar_spec.spl | 1 |
| test/unit/app/desugar/static_constants_spec.spl | 1 |
| test/unit/app/desugar/rewriter_static_calls_spec.spl | 1 |
| test/unit/app/desugar/rewriter_constants_spec.spl | 1 |
| test/unit/app/desugar/interface_desugar_spec.spl | 1 |
| test/unit/app/desugar/forwarding_spec.spl | 1 |
| test/unit/app/desugar/context_params_spec.spl | 1 |
| test/unit/app/dap/server_hooks_integration_spec.spl | 1 |
| test/unit/app/dap/interpreter_hooks_spec.spl | 1 |
| test/unit/app/dap/dap_spec.spl | 1 |
| test/unit/app/cli/query_sem_query_integration_spec.spl | 1 |
| test/unit/app/cli/query_ast_query_integration_spec.spl | 1 |
| test/unit/app/cli_parser_spec.spl | 1 |
| test/integration/spec/runner_spec.spl | 1 |
| test/integration/compiler/static_method_desugar_spec.spl | 1 |
| test/feature/usage/pass_variants_spec.spl | 1 |
| test/03_system/feature/compiler/driver_native_spec.spl | 1 |
| test/03_system/feature/app/codegen_parity_completion_spec.spl | 1 |
| test/01_unit/tools/shell/test_spec.spl | 1 |
| test/01_unit/std/mock_spec.spl | 1 |
| test/01_unit/std/feature_validation/testing_framework_spec.spl | 1 |
| test/01_unit/lib/torch_spec.spl | 1 |
| test/01_unit/lib/pure/training_spec.spl | 1 |
| test/01_unit/lib/pure/training_extended_spec.spl | 1 |
| test/01_unit/lib/pure/optim/scheduler_spec.spl | 1 |
| test/01_unit/lib/pure/nn/serialization_spec.spl | 1 |
| test/01_unit/lib/pure/nn/pooling_spec.spl | 1 |
| test/01_unit/lib/pure/nn/pooling_integration_spec.spl | 1 |
| test/01_unit/lib/pure/nn/norm_spec.spl | 1 |
| test/01_unit/lib/pure/nn/loss_spec.spl | 1 |
| test/01_unit/lib/pure/nn/init_spec.spl | 1 |
| test/01_unit/lib/pure/nn/functional_spec.spl | 1 |
| test/01_unit/lib/pure/nn_extended_spec.spl | 1 |
| test/01_unit/lib/pure/nn/embedding_spec.spl | 1 |
| test/01_unit/lib/pure/nn/embedding_integration_spec.spl | 1 |
| test/01_unit/lib/pure/nn/embedding_backward_spec.spl | 1 |
| test/01_unit/lib/pure/nn/conv_spec.spl | 1 |
| test/01_unit/lib/pure/nn/conv_integration_spec.spl | 1 |
| test/01_unit/lib/pure/nn/attention_spec.spl | 1 |
| test/01_unit/lib/pure/data_loader_spec.spl | 1 |
| test/01_unit/lib/pure/autograd_extended_spec.spl | 1 |
| test/01_unit/lib/pure/autograd_advanced_spec.spl | 1 |
| test/01_unit/lib/ptr/ptr_spec.spl | 1 |
| test/01_unit/lib/physics/vector_spec.spl | 1 |
| test/01_unit/lib/physics/spatial_hash_spec.spl | 1 |
| test/01_unit/lib/physics/shapes_spec.spl | 1 |
| test/01_unit/lib/physics/rigidbody_spec.spl | 1 |
| test/01_unit/lib/physics/materials_spec.spl | 1 |
| test/01_unit/lib/physics/contact_spec.spl | 1 |
| test/01_unit/lib/physics/aabb_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/test_ffi_operator_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/simple_math_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/pure_load_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/fft_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/data_pipeline_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/custom_autograd_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/async_training_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/ml/activation_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/io/event_loop_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/game3d/physics_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/game3d/material_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/game3d/input_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/game3d/assets_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/async_host_mt_spec.spl | 1 |
| test/01_unit/lib/nogc_async_mut/async_embedded_spec.spl | 1 |
| test/01_unit/lib/ml/test_ffi_operator_spec.spl | 1 |
| test/01_unit/lib/ml/simple_math_spec.spl | 1 |
| test/01_unit/lib/ml/fft_spec.spl | 1 |
| test/01_unit/lib/ml/custom_autograd_spec.spl | 1 |
| test/01_unit/lib/ml/activation_spec.spl | 1 |
| test/01_unit/lib/i18n/resource_bundle_spec.spl | 1 |
| test/01_unit/lib/gc_async_mut/dl/config_spec.spl | 1 |
| test/01_unit/lib/gc_async_mut/dl/config_loader_spec.spl | 1 |
| test/01_unit/lib/common/tap_spec.spl | 1 |
| test/01_unit/lib/common/string_compiled_spec.spl | 1 |
| test/01_unit/lib/common/.sspec_wrapped_entry_error_format_spec.spl | 1 |
| test/01_unit/lib/common/seq_ce_spec.spl | 1 |
| test/01_unit/lib/common/seq_ce_e2e_spec.spl | 1 |
| test/01_unit/lib/common/repr_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/serialization_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/pooling_integration_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/embedding_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/embedding_integration_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/embedding_backward_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/conv_integration_spec.spl | 1 |
| test/01_unit/lib/common/pure/nn/attention_spec.spl | 1 |
| test/01_unit/lib/common/phantom_spec.spl | 1 |
| test/01_unit/lib/common/mock_spec.spl | 1 |
| test/01_unit/lib/common/iterable_spec.spl | 1 |
| test/01_unit/lib/common/feature_validation/testing_framework_spec.spl | 1 |
| test/01_unit/lib/common/error_trace_spec.spl | 1 |
| test/01_unit/compiler/type/runtime_type_check_spec.spl | 1 |
| test/01_unit/compiler/type_inference/variance_inference_spec.spl | 1 |
| test/01_unit/compiler/type_inference/type_infer_comprehensive_spec.spl | 1 |
| test/01_unit/compiler/type_inference/bidir_type_check_spec.spl | 1 |
| test/01_unit/compiler/type_checker/type_inference_executable_spec.spl | 1 |
| test/01_unit/compiler/traits/associated_types_trait_spec.spl | 1 |
| test/01_unit/compiler/target/target_spec_spec.spl | 1 |
| test/01_unit/compiler/semantics/safety_checker_spec.spl | 1 |
| test/01_unit/compiler/semantics/resolve_spec.spl | 1 |
| test/01_unit/compiler/semantics/effect_inference_spec.spl | 1 |
| test/01_unit/compiler/semantics/comptime_spec.spl | 1 |
| test/01_unit/compiler/semantics/closure_capture_warning_spec.spl | 1 |
| test/01_unit/compiler/semantics/call_graph_spec.spl | 1 |
| test/01_unit/compiler/semantics/borrow_check_spec.spl | 1 |
| test/01_unit/compiler/semantics/arch_rules_syntax_spec.spl | 1 |
| test/01_unit/compiler/semantics/alloc_inference_spec.spl | 1 |
| test/01_unit/compiler/parser/struct_update_spec.spl | 1 |
| test/01_unit/compiler/parser/parser_step_spec.spl | 1 |
| test/01_unit/compiler/parser/parser_outline_spec.spl | 1 |
| test/01_unit/compiler/parser/parser_new_spec.spl | 1 |
| test/01_unit/compiler/parser/parser_factory_spec.spl | 1 |
| test/01_unit/compiler/parser/parse_formats_spec.spl | 1 |
| test/01_unit/compiler/parser/parse_error_spec.spl | 1 |
| test/01_unit/compiler/parser/lexer_contextual_keywords_spec.spl | 1 |
| test/01_unit/compiler/parser/grammar_compile_spec.spl | 1 |
| test/01_unit/compiler/parser/dyn_trait_spec.spl | 1 |
| test/01_unit/compiler/parser/do_block_spec.spl | 1 |
| test/01_unit/compiler/parser/defer_spec.spl | 1 |
| test/01_unit/compiler/parser/ast_debug_spec.spl | 1 |
| test/01_unit/compiler/native/native_compile_spec.spl | 1 |
| test/01_unit/compiler/native/cli_interpreter_path_spec.spl | 1 |
| test/01_unit/compiler/native/auto_vectorize_spec.spl | 1 |
| test/01_unit/compiler/native/arm_neon_spec.spl | 1 |
| test/01_unit/compiler/mono/note_sdn_spec.spl | 1 |
| test/01_unit/compiler/mono/note_sdn_bdd_spec.spl | 1 |
| test/01_unit/compiler/mono/monomorphize_spec.spl | 1 |
| test/01_unit/compiler/mono/mono_cache_efficiency_spec.spl | 1 |
| test/01_unit/compiler/mir/mir_serialization_spec.spl | 1 |
| test/01_unit/compiler/mir/mir_opt_spec.spl | 1 |
| test/01_unit/compiler/mir/mir_enum_access_spec.spl | 1 |
| test/01_unit/compiler/mir/mir_data_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/vc_static_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/vc_import_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/doc_validation_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/cross_query_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/construct_types_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/construct_checker_spec.spl | 1 |
| test/01_unit/compiler/mdsoc/config_multi_dim_spec.spl | 1 |
| test/01_unit/compiler/macros/macro_integration_spec.spl | 1 |
| test/01_unit/compiler/linker/swa_zip_spec.spl | 1 |
| test/01_unit/compiler/hir/hir_new_spec.spl | 1 |
| test/01_unit/compiler/hir/hir_lowering_spec.spl | 1 |
| test/01_unit/compiler/hir/hir_async_spec.spl | 1 |
| test/01_unit/compiler/hir/hir_async_integration_spec.spl | 1 |
| test/01_unit/compiler/hir/hir_async_errors_spec.spl | 1 |
| test/01_unit/compiler/driver/pipeline_var_spec.spl | 1 |
| test/01_unit/compiler/driver/pipeline_mir_spec.spl | 1 |
| test/01_unit/compiler/driver/pipeline_basic_spec.spl | 1 |
| test/01_unit/compiler/driver/driver_spec.spl | 1 |
| test/01_unit/compiler/driver/compiler_shared_di_check_spec.spl | 1 |
| test/01_unit/compiler/di/di_validation_spec.spl | 1 |
| test/01_unit/compiler/di/di_runtime_spec.spl | 1 |
| test/01_unit/compiler/di/di_proxy_spec.spl | 1 |
| test/01_unit/compiler/di/di_config_spec.spl | 1 |
| test/01_unit/compiler/dependency/visibility_spec.spl | 1 |
| test/01_unit/compiler/dependency/visibility_integration_spec.spl | 1 |
| test/01_unit/compiler/dependency/symbol_spec.spl | 1 |
| test/01_unit/compiler/dependency/resolution_spec.spl | 1 |
| test/01_unit/compiler/dependency/macro_import_theorems_spec.spl | 1 |
| test/01_unit/compiler/dependency/integration_spec.spl | 1 |
| test/01_unit/compiler/dependency/import_resolution_spec.spl | 1 |
| test/01_unit/compiler/dependency/graph_transitive_spec.spl | 1 |
| test/01_unit/compiler/dependency/graph_topo_spec.spl | 1 |
| test/01_unit/compiler/dependency/graph_cycles_spec.spl | 1 |
| test/01_unit/compiler/dependency/graph_basic_spec.spl | 1 |
| test/01_unit/compiler_core/structural_subtyping_spec.spl | 1 |
| test/01_unit/compiler_core/parser_spec.spl | 1 |
| test/01_unit/compiler_core/parser_option_coverage_spec.spl | 1 |
| test/01_unit/compiler_core/parser_intensive_spec.spl | 1 |
| test/01_unit/compiler_core/lexer_intensive_spec.spl | 1 |
| test/01_unit/compiler_core/eager_yield_spec.spl | 1 |
| test/01_unit/compiler_core/branch_coverage_36_spec.spl | 1 |
| test/01_unit/compiler_core/branch_coverage_33_spec.spl | 1 |
| test/01_unit/compiler_core/branch_coverage_31_spec.spl | 1 |
| test/01_unit/compiler_core/ast_spec.spl | 1 |
| test/01_unit/compiler/config/literal_config_spec.spl | 1 |
| test/01_unit/compiler/config/error_formatter_spec.spl | 1 |
| test/01_unit/compiler/blocks/utils_spec.spl | 1 |
| test/01_unit/compiler/blocks/pre_lex_per_dsl_spec.spl | 1 |
| test/01_unit/compiler/blocks/pre_lex_info_spec.spl | 1 |
| test/01_unit/compiler/blocks/easy_api_spec.spl | 1 |
| test/01_unit/compiler/blocks/builder_api_spec.spl | 1 |
| test/01_unit/compiler/blocks/block_skip_policy_spec.spl | 1 |
| test/01_unit/compiler/blocks/block_outline_info_spec.spl | 1 |
| test/01_unit/compiler/blocks/block_definition_three_level_spec.spl | 1 |
| test/01_unit/compiler/backend/llvm_wasm_spec.spl | 1 |
| test/01_unit/compiler/backend/llvm_lib_backend_spec.spl | 1 |
| test/01_unit/compiler/backend/instruction_coverage_spec.spl | 1 |
| test/01_unit/compiler/backend/expression_evaluator_spec.spl | 1 |
| test/01_unit/compiler/backend/execution_manager_spec.spl | 1 |
| test/01_unit/compiler/backend/differential_testing_spec.spl | 1 |
| test/01_unit/compiler/backend/differential_backend_consistency_spec.spl | 1 |
| test/01_unit/compiler/backend/backend_orchestration_spec.spl | 1 |
| test/01_unit/compiler/backend/backend_factory_spec.spl | 1 |
| test/01_unit/compiler/async/suspension_analysis_spec.spl | 1 |
| test/01_unit/compiler/async/state_enum_spec.spl | 1 |
| test/01_unit/compiler/async/poll_generator_spec.spl | 1 |
| test/01_unit/compiler/async/async_state_machine_spec.spl | 1 |
| test/01_unit/compiler/async/async_pipeline_spec.spl | 1 |
| test/01_unit/compiler/async/async_mir_spec.spl | 1 |
| test/01_unit/compiler/async/async_frame_analysis_spec.spl | 1 |
| test/01_unit/compiler/async/async_desugar_integration_spec.spl | 1 |
| test/01_unit/app/mcp_unit/prompts_compiled_spec.spl | 1 |
| test/01_unit/app/mcp_unit/outline_renderer_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_tools_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_tasks_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_subscriptions_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_structured_output_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_server_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_sampling_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_jj_commit_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_dx_helpers_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_debug_tools_spec.spl | 1 |
| test/01_unit/app/mcp_unit/mcp_completions_intensive_spec.spl | 1 |
| test/01_unit/app/mcp_unit/fileio_temp_spec.spl | 1 |
| test/01_unit/app/mcp_unit/fileio_lite_safe_read_spec.spl | 1 |
| test/01_unit/app/mcp_unit/failure_analysis_spec.spl | 1 |
| test/01_unit/app/mcp_unit/editor_spec.spl | 1 |
| test/01_unit/app/mcp_unit/di_integration_spec.spl | 1 |
| test/01_unit/app/mcp_unit/capabilities_spec.spl | 1 |
| test/01_unit/app/lsp/server_query_integration_spec.spl | 1 |
| test/01_unit/app/lsp/server_lifecycle_spec.spl | 1 |
| test/01_unit/app/lsp/references_spec.spl | 1 |
| test/01_unit/app/lsp/message_dispatcher_spec.spl | 1 |
| test/01_unit/app/lsp/hover_spec.spl | 1 |
| test/01_unit/app/lsp/hover_handler_spec.spl | 1 |
| test/01_unit/app/lsp/folding_range_spec.spl | 1 |
| test/01_unit/app/lsp/document_sync_spec.spl | 1 |
| test/01_unit/app/lsp/compiler_query_api_spec.spl | 1 |
| test/01_unit/app/leak_check/types_spec.spl | 1 |
| test/01_unit/app/io/window_ffi_spec.spl | 1 |
| test/01_unit/app/io/regex_sffi_spec.spl | 1 |
| test/01_unit/app/io/rapier2d_ffi_spec.spl | 1 |
| test/01_unit/app/io/process_limits_basic_spec.spl | 1 |
| test/01_unit/app/io/jit_availability_spec.spl | 1 |
| test/01_unit/app/io/http_ffi_spec.spl | 1 |
| test/01_unit/app/io/graphics2d_ffi_spec.spl | 1 |
| test/01_unit/app/io/gamepad_ffi_spec.spl | 1 |
| test/01_unit/app/io/file_ops_rw_spec.spl | 1 |
| test/01_unit/app/io/dir_ops_create_list_spec.spl | 1 |
| test/01_unit/app/io/audio_ffi_spec.spl | 1 |
| test/01_unit/app/interpreter/persistent_vec_spec.spl | 1 |
| test/01_unit/app/interpreter/persistent_dict_spec.spl | 1 |
| test/01_unit/app/interpreter/lazy_seq_spec.spl | 1 |
| test/01_unit/app/interpreter/debug_spec.spl | 1 |
| test/01_unit/app/interpreter/class_method_call_spec.spl | 1 |
| test/01_unit/app/grammar_doc/doc_generator_spec.spl | 1 |
| test/01_unit/app/ffi_gen/module_gen_spec.spl | 1 |
| test/01_unit/app/diagram/call_flow_profiling_spec.spl | 1 |
| test/01_unit/app/devtools/devtools_cli_spec.spl | 1 |
| test/01_unit/app/desugar/trait_static_dispatch_spec.spl | 1 |
| test/01_unit/app/desugar/trait_scanner_spec.spl | 1 |
| test/01_unit/app/desugar/struct_defaults_spec.spl | 1 |
| test/01_unit/app/desugar/static_methods_desugar_spec.spl | 1 |
| test/01_unit/app/desugar/static_constants_spec.spl | 1 |
| test/01_unit/app/desugar/rewriter_static_calls_spec.spl | 1 |
| test/01_unit/app/desugar/rewriter_constants_spec.spl | 1 |
| test/01_unit/app/desugar/interface_desugar_spec.spl | 1 |
| test/01_unit/app/desugar/forwarding_spec.spl | 1 |
| test/01_unit/app/desugar/context_params_spec.spl | 1 |

## Second pass, 2026-08-04 — coupling gate applied, 15 specs landed

This section supersedes the triage above for the files it names. It re-ran the
whole canonical family (`test/01_unit`, `test/02_integration`, `test/03_system`:
246 files carrying `pending_reason`) rather than the 94-file subset, so its
class counts are larger and were measured independently.

### The measurement was invalid before b3a3f804b6c

Four tracked symlinks pointed at an ABSOLUTE path inside one developer's
checkout, `/home/ormastes/dev/pub/simple/src/...`:

    test/01_unit/app/desugar/app     test/unit/app/desugar/app
    test/01_unit/lib/database/lib    test/unit/lib/database/lib

They entered main in 7f5a55fa46e, the 2026-08-01 restore after the
truncated-tree wipe. In a second worktree they resolve back into the ORIGINAL
clone, so a spec appears to exercise the worktree's source while actually
running another checkout's. Every coupling result taken in a worktree before
that fix is fail-open. Demonstrated by value: with the absolute link, renaming
all 16 `fn`s in `src/app/desugar/context_params.spl` left
`context_params_spec` at exactly `14 examples, 5 failures`; DELETING the module
file outright also left it at `14 examples, 5 failures`. After repointing the
link, the same rename gives `14 examples, 14 failures`. On a fresh clone or CI
runner the links simply dangle. Fixed in b3a3f804b6c.

### Gate used

Rename every top-level `fn` (and `class`/`struct`/`enum`) in the module the
spec names; require the example count to HOLD (proving the module still loads
and no describe was dropped) and the failure count to RISE. Two refinements the
earlier pass did not have:

- The count-and-failure gate is fail-open when the only examples touching the
  module are ALREADY failing. `interface_desugar_spec` against
  `trait_desugar.spl` stays at `9 examples, 2 failures` under the rename and
  reads NOT-COUPLED, yet the two failure MESSAGES change from a value mismatch
  to `semantic: function 'desugar_traits' not found`. Compare messages, not
  just counts, whenever the delta is zero.
- A `print` probe inside the production function is NOT a valid binding check:
  the spec runner captures example stdout, so the marker never appears and the
  probe reads as 'never entered' regardless. `strace` is also unavailable in
  this sandbox and produces an EMPTY log, which reads the same way. Both nearly
  produced a false 'uncoupled' verdict here.

### Landed (15 specs, 8 commits)

| Spec | before | after | commit |
|---|---|---|---|
| `test/01_unit/app/desugar/context_params_spec.spl` (+ `test/unit/…`) | 1 example (tautology) | 14 examples, 0 failures | 27f50e28fcf |
| `test/01_unit/app/desugar/rewriter_constants_spec.spl` (+ `test/unit/…`) | 1 example | 32 examples, 0 failures | 7c40b71e170 |
| `test/01_unit/app/desugar/rewriter_static_calls_spec.spl` (+ `test/unit/…`) | 1 example | 41 examples, 0 failures | 7c40b71e170 |
| `test/01_unit/app/desugar/static_constants_spec.spl` (+ `test/unit/…`) | 1 example | 29 examples, 1 failure | 9a7d7f8e3b3 |
| `test/01_unit/app/desugar/interface_desugar_spec.spl` (+ `test/unit/…`) | 1 example | 9 examples, 2 failures | 386e1043706 |
| `test/01_unit/app/desugar/forwarding_spec.spl` (+ `test/unit/…`) | 1 example | 15 examples, 0 failures | faea633557a |
| `test/01_unit/app/desugar/static_methods_desugar_spec.spl` (+ `test/unit/…`) | 1 example | 28 examples, 0 failures | faea633557a |
| `test/01_unit/app/desugar/struct_defaults_spec.spl` (+ `test/unit/…`) | 1 example | 14 examples, 0 failures | faea633557a |
| `test/01_unit/app/desugar/trait_scanner_spec.spl` (+ `test/unit/…`) | 1 example | 9 examples, 0 failures | faea633557a |
| `test/01_unit/app/desugar/trait_static_dispatch_spec.spl` (+ `test/unit/…`) | 1 example | 12 examples, 0 failures | faea633557a |
| `test/01_unit/compiler_core/lexer_intensive_spec.spl` (+ `test/unit/…`) | 1 example | 60 examples, 1 failure | 85a51c4adeb |
| `test/01_unit/compiler_core/parser_spec.spl` (+ `test/unit/…`) | 1 example | 24 examples, 2 failures | 98df0e31049 |
| `test/01_unit/compiler_core/parser_option_coverage_spec.spl` (+ `test/unit/…`) | 1 example | 29 examples, 0 failures | 011d509151d |
| `test/01_unit/compiler_core/parser_intensive_spec.spl` (+ `test/unit/…`) | 1 example | 40 examples, 1 failure | 011d509151d |
| `test/01_unit/compiler_core/ast_spec.spl` (+ `test/unit/…`) | 1 example | 11 examples, 3 failures | 67fa0ab1f2a |

Per canonical copy: **15 vacuous passing examples -> 367 real examples, 357
passing and 10 honestly failing.** Doubled by the byte-identical `test/unit`
mirrors: 30 -> 734, and **20 examples the repo previously reported as green are
now red.** Every one of those 20 is a defect that existed before this work; none
is a regression.

### Production defects found and fixed

- 27f50e28fcf — `with_context` was NEVER desugared when any argument carried a
  colon, i.e. for its entire intended input set. `_find_char(trimmed, ":")`
  took the `name:` separator inside the parentheses as the block colon, so the
  guard saw no `)` before it and the pass returned the line untouched. Only the
  degenerate `with_context(logger):` form worked. Second defect in the same
  pass: a nested `with_context` was never rewritten. Sabotage: making
  `_find_matching_paren` return -1 reproduces the original 5 failures exactly.
- 7c40b71e170 — the static-call rewriter dropped any single-character member
  that ended a line (`Defaults.B` unchanged, `Defaults.B ` with a trailing
  space rewritten) from an `after_ident + 2 < llen` guard that should have been
  `+ 1`; and it never chained, so `Outer.Inner.CONSTANT` collapsed only one
  level to `Outer__Inner.CONSTANT`.
- 98df0e31049 — `parser_error_count()` returned a literal `0` and
  `parser_get_errors()` a fresh `[]`, always: `par_errors` was declared,
  cleared and exported but never pushed to. A caller gating on the COUNT saw a
  clean parse no matter how many errors were printed. This is the THIRD fix in
  this family — `par_had_error_mirror` and `par_first_error_mirror` both routed
  around the count and the list instead of filling them in.

### Honest reds landed (10 examples per copy)

| Spec | example | why |
|---|---|---|
| static_constants_spec | handles nested impl blocks correctly | pass does not descend into a nested impl and MIS-ATTRIBUTES the inner constant as `Outer__Y`; Simple has no nested impl, so the input cannot reach the pass from the real pipeline |
| interface_desugar_spec | interface desugars to struct with fn-fields | `desugar_traits` matches only `trait `; an `interface` header falls through untouched, though `trait_scanner.spl` fully understands the form |
| interface_desugar_spec | impl Interface for value generates factory | the module header documents `impl T for X: -> fn X_as_T()`; no factory generation exists anywhere in the file |
| lexer_intensive_spec | emits attribute token for #[ | `"#[test]\n"` lexes to `[TOK_EOF]` alone. `TOK_HASH_LBRACKET` has exactly 2 references in all of `src/`: its declaration and its export. Nothing produces or consumes it |
| parser_spec | parses a mixed module | 6 declared top-level forms produce 7 decls |
| parser_spec | parses module-level expression as pseudo-decl | `decls=1 tag=4 bodylen=1 errors=false`, but reading the one body stmt aborts with `[stmt_get_tag] OOB idx=2 arena_len=0 arena_gen=6` — an AST-arena lifetime bug |
| parser_intensive_spec | parses strings with and without interpolation | via `parser_init`+`parse_expr`, `"hi"`, `"hi {n}!"` and unterminated `"hi {n"` ALL return tag 3 (EXPR_STRING_LIT); 34 is never produced on this path |
| ast_spec | creates arrays, tuples, dicts | `expr_get_args()` on a 2-element array literal returns 1 |
| ast_spec | creates struct literals and ranges | `expr_get_extra()` on a range returns -1, expected 1 |
| ast_spec | creates functions and structs | `expr_func_decl` arity: spec and implementation disagree on `type_params` |

### A spec-literal trap that made three examples unrunnable

`{...}` inside a `.spl` text literal INTERPOLATES. Three specs embedded sample
source containing braces — `"print \"Value: {Config.DEFAULT_VALUE}\""`,
`static val FORMAT = \"({x}, {y})\"`, `"hello {name}!"` — so the example died
with `semantic: variable 'Config'/'x'/'name' not found` BEFORE reaching its
subject. Doubling the braces (`{{`) yields the intended single-brace text.
Any spec in this family that carries Simple source in a literal is suspect.

### Remaining inventory (mechanically restored and executed, 2026-08-04)

Counts are `examples / failures` from a restore-and-run of the canonical copy,
BEFORE any coupling gate. A green line here is NOT evidence of coverage —
`safety_checker_spec` restores to 26 green examples whose every assertion is
`check(<the test's own string literal>.contains(...))`, and
`devtools_cli_spec` to 9 x `check(true)`. None of the files below has passed a
coupling gate; none should be landed until it does.

#### Mixed — real defects exposed (21 files)

| Spec | examples | failures |
|---|---|---|
| test/01_unit/compiler/blocks/block_definition_three_level_spec.spl | 70 | 67 |
| test/01_unit/app/io/gamepad_ffi_spec.spl | 61 | 22 |
| test/01_unit/app/io/graphics2d_ffi_spec.spl | 59 | 52 |
| test/01_unit/compiler/driver/driver_spec.spl | 59 | 9 |
| test/01_unit/compiler/blocks/pre_lex_info_spec.spl | 49 | 47 |
| test/01_unit/compiler/backend/instruction_coverage_spec.spl | 47 | 35 |
| test/01_unit/app/io/http_ffi_spec.spl | 45 | 14 |
| test/01_unit/app/io/window_ffi_spec.spl | 42 | 39 |
| test/01_unit/app/io/rapier2d_ffi_spec.spl | 39 | 9 |
| test/01_unit/compiler/native/arm_neon_spec.spl | 39 | 21 |
| test/01_unit/compiler/blocks/block_outline_info_spec.spl | 37 | 32 |
| test/01_unit/compiler/backend/backend_factory_spec.spl | 35 | 34 |
| test/01_unit/compiler/mono/mono_cache_efficiency_spec.spl | 35 | 5 |
| test/01_unit/compiler/backend/backend_orchestration_spec.spl | 34 | 21 |
| test/01_unit/compiler/blocks/pre_lex_per_dsl_spec.spl | 32 | 26 |
| test/01_unit/compiler/mdsoc/construct_checker_spec.spl | 29 | 11 |
| test/01_unit/compiler/backend/differential_testing_spec.spl | 27 | 23 |
| test/01_unit/compiler/dependency/import_resolution_spec.spl | 24 | 17 |
| test/01_unit/app/io/file_ops_rw_spec.spl | 12 | 1 |
| test/01_unit/app/leak_check/types_spec.spl | 10 | 1 |
| test/01_unit/compiler/di/di_proxy_spec.spl | 10 | 5 |

#### All-red (19 files)

| Spec | examples | failures |
|---|---|---|
| test/01_unit/compiler/mdsoc/construct_types_spec.spl | 68 | 68 |
| test/01_unit/app/io/audio_ffi_spec.spl | 61 | 61 |
| test/01_unit/compiler/dependency/resolution_spec.spl | 35 | 35 |
| test/01_unit/compiler/dependency/graph_basic_spec.spl | 33 | 33 |
| test/01_unit/app/lsp/message_dispatcher_spec.spl | 29 | 29 |
| test/01_unit/app/io/regex_sffi_spec.spl | 25 | 25 |
| test/01_unit/compiler/semantics/alloc_inference_spec.spl | 23 | 23 |
| test/01_unit/compiler/mdsoc/config_multi_dim_spec.spl | 22 | 22 |
| test/01_unit/compiler/semantics/closure_capture_warning_spec.spl | 22 | 22 |
| test/01_unit/compiler/semantics/call_graph_spec.spl | 21 | 21 |
| test/01_unit/compiler/mdsoc/cross_query_spec.spl | 19 | 19 |
| test/01_unit/app/lsp/document_sync_spec.spl | 18 | 18 |
| test/01_unit/compiler/dependency/symbol_spec.spl | 18 | 18 |
| test/01_unit/app/lsp/server_lifecycle_spec.spl | 17 | 17 |
| test/01_unit/compiler/dependency/graph_cycles_spec.spl | 16 | 16 |
| test/01_unit/compiler/dependency/graph_transitive_spec.spl | 15 | 15 |
| test/01_unit/compiler/dependency/graph_topo_spec.spl | 13 | 13 |
| test/01_unit/compiler/dependency/integration_spec.spl | 7 | 7 |
| test/01_unit/compiler/blocks/easy_api_spec.spl | 3 | 3 |

#### Restores green — coupling UNPROVEN, do not land as-is (9 files)

| Spec | examples | failures |
|---|---|---|
| test/01_unit/compiler/semantics/safety_checker_spec.spl | 26 | 0 |
| test/01_unit/app/io/dir_ops_create_list_spec.spl | 12 | 0 |
| test/01_unit/app/devtools/devtools_cli_spec.spl | 11 | 0 |
| test/01_unit/compiler/mdsoc/doc_validation_spec.spl | 5 | 0 |
| test/01_unit/lib/gc_async_mut/dl/config_loader_spec.spl | 2 | 0 |
| test/01_unit/lib/gc_async_mut/dl/config_spec.spl | 2 | 0 |
| test/01_unit/lib/nogc_async_mut/async_host_mt_spec.spl | 2 | 0 |
| test/01_unit/lib/pure/data_loader_spec.spl | 2 | 0 |
| test/01_unit/app/io/jit_availability_spec.spl | 1 | 0 |

#### Will not load (stale module/API paths) — 0 examples (181 files)

| Spec |
|---|
| test/01_unit/app/diagram/call_flow_profiling_spec.spl |
| test/01_unit/app/ffi_gen/module_gen_spec.spl |
| test/01_unit/app/grammar_doc/doc_generator_spec.spl |
| test/01_unit/app/interpreter/class_method_call_spec.spl |
| test/01_unit/app/interpreter/debug_spec.spl |
| test/01_unit/app/interpreter/lazy_seq_spec.spl |
| test/01_unit/app/interpreter/persistent_dict_spec.spl |
| test/01_unit/app/interpreter/persistent_vec_spec.spl |
| test/01_unit/app/io/process_limits_basic_spec.spl |
| test/01_unit/app/lsp/compiler_query_api_spec.spl |
| test/01_unit/app/lsp/folding_range_spec.spl |
| test/01_unit/app/lsp/hover_handler_spec.spl |
| test/01_unit/app/lsp/hover_spec.spl |
| test/01_unit/app/lsp/references_spec.spl |
| test/01_unit/app/lsp/server_query_integration_spec.spl |
| test/01_unit/app/mcp_unit/capabilities_spec.spl |
| test/01_unit/app/mcp_unit/di_integration_spec.spl |
| test/01_unit/app/mcp_unit/editor_spec.spl |
| test/01_unit/app/mcp_unit/failure_analysis_spec.spl |
| test/01_unit/app/mcp_unit/fileio_lite_safe_read_spec.spl |
| test/01_unit/app/mcp_unit/fileio_temp_spec.spl |
| test/01_unit/app/mcp_unit/mcp_completions_intensive_spec.spl |
| test/01_unit/app/mcp_unit/mcp_debug_tools_spec.spl |
| test/01_unit/app/mcp_unit/mcp_dx_helpers_spec.spl |
| test/01_unit/app/mcp_unit/mcp_jj_commit_spec.spl |
| test/01_unit/app/mcp_unit/mcp_sampling_spec.spl |
| test/01_unit/app/mcp_unit/mcp_server_spec.spl |
| test/01_unit/app/mcp_unit/mcp_spec.spl |
| test/01_unit/app/mcp_unit/mcp_structured_output_spec.spl |
| test/01_unit/app/mcp_unit/mcp_subscriptions_spec.spl |
| test/01_unit/app/mcp_unit/mcp_tasks_spec.spl |
| test/01_unit/app/mcp_unit/mcp_tools_spec.spl |
| test/01_unit/app/mcp_unit/outline_renderer_spec.spl |
| test/01_unit/app/mcp_unit/prompts_compiled_spec.spl |
| test/01_unit/compiler/async/async_desugar_integration_spec.spl |
| test/01_unit/compiler/async/async_frame_analysis_spec.spl |
| test/01_unit/compiler/async/async_mir_spec.spl |
| test/01_unit/compiler/async/async_pipeline_spec.spl |
| test/01_unit/compiler/async/async_state_machine_spec.spl |
| test/01_unit/compiler/async/poll_generator_spec.spl |
| test/01_unit/compiler/async/state_enum_spec.spl |
| test/01_unit/compiler/async/suspension_analysis_spec.spl |
| test/01_unit/compiler/backend/differential_backend_consistency_spec.spl |
| test/01_unit/compiler/backend/execution_manager_spec.spl |
| test/01_unit/compiler/backend/expression_evaluator_spec.spl |
| test/01_unit/compiler/backend/llvm_lib_backend_spec.spl |
| test/01_unit/compiler/backend/llvm_wasm_spec.spl |
| test/01_unit/compiler/blocks/block_skip_policy_spec.spl |
| test/01_unit/compiler/blocks/builder_api_spec.spl |
| test/01_unit/compiler/blocks/utils_spec.spl |
| test/01_unit/compiler/config/error_formatter_spec.spl |
| test/01_unit/compiler/config/literal_config_spec.spl |
| test/01_unit/compiler/dependency/macro_import_theorems_spec.spl |
| test/01_unit/compiler/dependency/visibility_integration_spec.spl |
| test/01_unit/compiler/dependency/visibility_spec.spl |
| test/01_unit/compiler/di/di_config_spec.spl |
| test/01_unit/compiler/di/di_runtime_spec.spl |
| test/01_unit/compiler/di/di_validation_spec.spl |
| test/01_unit/compiler/driver/compiler_shared_di_check_spec.spl |
| test/01_unit/compiler/driver/pipeline_basic_spec.spl |
| test/01_unit/compiler/driver/pipeline_mir_spec.spl |
| test/01_unit/compiler/driver/pipeline_var_spec.spl |
| test/01_unit/compiler/hir/hir_async_errors_spec.spl |
| test/01_unit/compiler/hir/hir_async_integration_spec.spl |
| test/01_unit/compiler/hir/hir_async_spec.spl |
| test/01_unit/compiler/hir/hir_lowering_spec.spl |
| test/01_unit/compiler/hir/hir_new_spec.spl |
| test/01_unit/compiler/macros/macro_integration_spec.spl |
| test/01_unit/compiler/mdsoc/vc_import_spec.spl |
| test/01_unit/compiler/mdsoc/vc_static_spec.spl |
| test/01_unit/compiler/mir/mir_data_spec.spl |
| test/01_unit/compiler/mir/mir_enum_access_spec.spl |
| test/01_unit/compiler/mir/mir_opt_spec.spl |
| test/01_unit/compiler/mir/mir_serialization_spec.spl |
| test/01_unit/compiler/mono/monomorphize_spec.spl |
| test/01_unit/compiler/mono/note_sdn_bdd_spec.spl |
| test/01_unit/compiler/mono/note_sdn_spec.spl |
| test/01_unit/compiler/native/auto_vectorize_spec.spl |
| test/01_unit/compiler/native/cli_interpreter_path_spec.spl |
| test/01_unit/compiler/native/native_compile_spec.spl |
| test/01_unit/compiler/parser/ast_debug_spec.spl |
| test/01_unit/compiler/parser/defer_spec.spl |
| test/01_unit/compiler/parser/do_block_spec.spl |
| test/01_unit/compiler/parser/dyn_trait_spec.spl |
| test/01_unit/compiler/parser/grammar_compile_spec.spl |
| test/01_unit/compiler/parser/lexer_contextual_keywords_spec.spl |
| test/01_unit/compiler/parser/parse_error_spec.spl |
| test/01_unit/compiler/parser/parse_formats_spec.spl |
| test/01_unit/compiler/parser/parser_factory_spec.spl |
| test/01_unit/compiler/parser/parser_new_spec.spl |
| test/01_unit/compiler/parser/parser_outline_spec.spl |
| test/01_unit/compiler/parser/parser_step_spec.spl |
| test/01_unit/compiler/parser/struct_update_spec.spl |
| test/01_unit/compiler/semantics/arch_rules_syntax_spec.spl |
| test/01_unit/compiler/semantics/borrow_check_spec.spl |
| test/01_unit/compiler/semantics/comptime_spec.spl |
| test/01_unit/compiler/semantics/effect_inference_spec.spl |
| test/01_unit/compiler/semantics/resolve_spec.spl |
| test/01_unit/compiler/target/target_spec_spec.spl |
| test/01_unit/compiler/traits/associated_types_trait_spec.spl |
| test/01_unit/compiler/type/runtime_type_check_spec.spl |
| test/01_unit/compiler/type_checker/type_inference_executable_spec.spl |
| test/01_unit/compiler/type_inference/bidir_type_check_spec.spl |
| test/01_unit/compiler/type_inference/type_infer_comprehensive_spec.spl |
| test/01_unit/compiler/type_inference/variance_inference_spec.spl |
| test/01_unit/compiler_core/branch_coverage_31_spec.spl |
| test/01_unit/compiler_core/branch_coverage_33_spec.spl |
| test/01_unit/compiler_core/branch_coverage_36_spec.spl |
| test/01_unit/compiler_core/eager_yield_spec.spl |
| test/01_unit/compiler_core/must_use_spec.spl |
| test/01_unit/compiler_core/structural_subtyping_spec.spl |
| test/01_unit/lib/common/error_trace_spec.spl |
| test/01_unit/lib/common/iterable_spec.spl |
| test/01_unit/lib/common/mock_spec.spl |
| test/01_unit/lib/common/phantom_spec.spl |
| test/01_unit/lib/common/pure/nn/attention_spec.spl |
| test/01_unit/lib/common/pure/nn/conv_integration_spec.spl |
| test/01_unit/lib/common/pure/nn/embedding_backward_spec.spl |
| test/01_unit/lib/common/pure/nn/embedding_integration_spec.spl |
| test/01_unit/lib/common/pure/nn/embedding_spec.spl |
| test/01_unit/lib/common/pure/nn/pooling_integration_spec.spl |
| test/01_unit/lib/common/pure/nn/serialization_spec.spl |
| test/01_unit/lib/common/repr_spec.spl |
| test/01_unit/lib/common/seq_ce_e2e_spec.spl |
| test/01_unit/lib/common/seq_ce_spec.spl |
| test/01_unit/lib/common/string_compiled_spec.spl |
| test/01_unit/lib/common/tap_spec.spl |
| test/01_unit/lib/ml/activation_spec.spl |
| test/01_unit/lib/ml/custom_autograd_spec.spl |
| test/01_unit/lib/ml/fft_spec.spl |
| test/01_unit/lib/ml/simple_math_spec.spl |
| test/01_unit/lib/ml/test_ffi_operator_spec.spl |
| test/01_unit/lib/nogc_async_mut/async_embedded_spec.spl |
| test/01_unit/lib/nogc_async_mut/game3d/assets_spec.spl |
| test/01_unit/lib/nogc_async_mut/game3d/input_spec.spl |
| test/01_unit/lib/nogc_async_mut/game3d/material_spec.spl |
| test/01_unit/lib/nogc_async_mut/game3d/physics_spec.spl |
| test/01_unit/lib/nogc_async_mut/io/event_loop_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/activation_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/async_training_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/custom_autograd_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/data_pipeline_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/fft_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/pure_load_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/simple_math_spec.spl |
| test/01_unit/lib/nogc_async_mut/ml/test_ffi_operator_spec.spl |
| test/01_unit/lib/physics/aabb_spec.spl |
| test/01_unit/lib/physics/contact_spec.spl |
| test/01_unit/lib/physics/materials_spec.spl |
| test/01_unit/lib/physics/rigidbody_spec.spl |
| test/01_unit/lib/physics/shapes_spec.spl |
| test/01_unit/lib/physics/spatial_hash_spec.spl |
| test/01_unit/lib/physics/vector_spec.spl |
| test/01_unit/lib/ptr/ptr_spec.spl |
| test/01_unit/lib/pure/autograd_advanced_spec.spl |
| test/01_unit/lib/pure/autograd_extended_spec.spl |
| test/01_unit/lib/pure/nn/attention_spec.spl |
| test/01_unit/lib/pure/nn/conv_integration_spec.spl |
| test/01_unit/lib/pure/nn/conv_spec.spl |
| test/01_unit/lib/pure/nn/embedding_backward_spec.spl |
| test/01_unit/lib/pure/nn/embedding_integration_spec.spl |
| test/01_unit/lib/pure/nn/embedding_spec.spl |
| test/01_unit/lib/pure/nn/functional_spec.spl |
| test/01_unit/lib/pure/nn/init_spec.spl |
| test/01_unit/lib/pure/nn/loss_spec.spl |
| test/01_unit/lib/pure/nn/norm_spec.spl |
| test/01_unit/lib/pure/nn/pooling_integration_spec.spl |
| test/01_unit/lib/pure/nn/pooling_spec.spl |
| test/01_unit/lib/pure/nn/serialization_spec.spl |
| test/01_unit/lib/pure/nn_extended_spec.spl |
| test/01_unit/lib/pure/optim/scheduler_spec.spl |
| test/01_unit/lib/pure/training_extended_spec.spl |
| test/01_unit/lib/pure/training_spec.spl |
| test/01_unit/lib/torch_spec.spl |
| test/01_unit/os/crypto/ffdhe_kat_spec.spl |
| test/01_unit/std/mock_spec.spl |
| test/02_integration/baremetal/remote_riscv32_spec.spl |
| test/02_integration/compiler/llvm_backend_e2e_spec.spl |
| test/02_integration/compiler/llvm_compiled_proof_spec.spl |
| test/02_integration/compiler/llvm_native_link_spec.spl |
| test/02_integration/compiler/llvm_parity_spec.spl |

Dominant failure shapes in the two red classes, for triage:

- `semantic: unknown extern function: rt_*` — the FFI specs (audio, regex,
  gamepad, graphics2d, http, window). Identical under the default engine and
  under `SIMPLE_EXECUTION_MODE=interpret`, so NOT an interpreter artifact.
- `unknown static method new on class X` / `variable X not found` — the
  compiler/dependency (ImportGraph, FileSystem, ModPath, SymbolTable) and
  compiler/mdsoc (ConstructCapsule, CrossDimensionQuery) clusters. 7 + 4 files,
  ~275 examples, all-red.


## Third pass, 2026-08-05 — the 230 withheld specs, cause-level triage

This pass took the 230 the second pass withheld, starting with the 181 recorded
as "will not load (stale module/API paths) — 0 examples". **That classification
was wrong for 112 of the 181.** The bucket is three different populations, and
only one of them is a load failure.

### Correction 1 — 99 of the 181 are GUTTED files, not load failures

99 of the 181 are 4-to-6-line files containing nothing but the tautology guard.
There is no commented-out body to restore, so a mechanical restore yields an
empty file and the runner reports 0 examples. That reads identically to "will
not load" and is what the second pass recorded.

The real content is recoverable, but **not on the file's own path** — `git log
--follow` on each path returns a flat 168-263 bytes for its entire history and
says the content never existed. It survives elsewhere: enumerating every
`*_spec.spl` blob in the object graph (`git rev-list --all --objects`,
61,243 blobs) and matching by BASENAME finds a >1KB version for 92 of the 99.
Sources, in order of frequency: `.claude/worktrees/<name>/…` (24 — a developer
worktree that was accidentally committed), `.jjconflict-base-0/…` (18 — the
conflict trees the VCS guards exist to reject), pre-reorg `test/…` paths (4),
and `.migration_backup_20260111_125136/…` (2).

48 recover from a path whose last two components match the current path exactly
(e.g. `…/app/lsp/folding_range_spec.spl` -> `test/01_unit/app/lsp/folding_range_spec.spl`)
and are high-confidence. 44 more recover from a renamed directory
(`test/unit/app/mcp/` -> `test/01_unit/app/mcp_unit/`) and need per-file
judgement; at least one (`mcp_spec.spl` from
`test/03_system/tools/llm/claude_full/cli/handlers/`) is a same-named different
spec and must not be used. 7 have no content anywhere.

**Restoring the 48 high-confidence ones: 42 of 48 LOAD, giving 385 examples and
70 failures.** The "will not load" verdict was an artifact of restoring from the
wrong place.

### Correction 2 — 13 of the 181 already load and always did

13 files are live specs in which INDIVIDUAL `it` blocks were replaced by
tautology guards (2 to 18 guards per file), not whole-file comment-outs. They
load and run untouched: **280 examples, 18 failures.** They were recorded as
0 examples.

The likely cause of the miscount is `tail -1` on the verdict lines. A spec with
several `describe` blocks prints one verdict per block, and the last one is not
the total: `remote_riscv32_spec` reads `9 examples, 0 failures` on its last line
and `85 examples, 7 failures` when all lines are summed — a 9x undercount. Sum
every `^N examples?, M failures?$` line; never take the last.

### The 69 that genuinely do not load — cause distribution

| Cause | Files |
|---|---|
| `Module "compiler" does not export '<mod>'` — flat pre-layer-split import | 39 |
| `Cannot resolve module: <name>` (module does not exist anywhere) | 22 |
| Parse error in the restored body | 5 |
| Other (`use std.ffi` deprecated, no `main`, misc) | 3 |

The 39-file bucket is one cause. `src/compiler/` was reorganised into numbered
layer directories (`00.common`, `10.frontend`, `20.hir`, …) with unnumbered
symlinks alongside (`frontend -> 10.frontend`). The canonical import is
`use compiler.frontend.parser_types` — 38 uses in `src/`. These specs still say
`use compiler.parser_types` (18 uses in `test/`) or `use compiler.core.parser_types`
(8 uses), naming a `core` directory that no longer exists.

**Cause-level fix: rewrite `compiler.<mod>` and `compiler.core.<mod>` to
`compiler.<layer>.<mod>`, resolving each module name to its actual layer
directory. This unblocked 27 of the 69 specs -> 459 examples, 176 failures.**

The 22 `Cannot resolve module` failures name modules that do not exist in the
tree at all: `std.test` (4), `std.phantom` (1), `physics.core*` (7 — the real
path is `lib.nogc_async_mut.engine.physics`), `simple.compiler.monomorphize.note_sdn`
(2), `app.ffi_gen.types` (1). The last is worth its own note: `src/app/ffi_gen/`
now contains only 9 `test_*.spl` files — `types.spl`, `module_gen.spl`,
`enum_gen.spl` and `fn_gen.spl` are all gone, so `module_gen_spec` can never
load. Its subject was deleted.

### Coupling gate — 9 specs pass, and the gate was fail-open twice first

Gate: rename every top-level `fn` in the production modules the spec imports;
require the example count to HOLD and failures to RISE (or the failure messages
to change).

**The gate read UNCOUPLED on all 23 candidates before it worked at all.** Two
independent resolution bugs, each of which renamed ZERO functions and therefore
compared a run against itself:

1. `use std.pure.nn.pooling.{...}` was captured with a trailing dot, so the
   module path became `pure/nn/pooling/` and matched nothing.
2. `compiler.frontend.parser_types` resolves through the `frontend -> 10.frontend`
   SYMLINK, and `find` does not follow symlinks, so `*/compiler/frontend/*.spl`
   never matched a real path. Layer lookup has to go through the numbered name.

Both produced a clean, plausible `UNCOUPLED` verdict with the counts printed.
The tell is the renamed-function count: it must be reported alongside the
verdict, and a gate that renamed 0 functions is not a result.

A cheaper structural pre-filter catches most of it without running anything:
**17 of the 23 green candidates import no production module at all.**
`runtime_type_check_spec` (33 examples) imports only `std.spec`, then declares
its own `test_val_kinds` / `TEST_VAL_*` mocks with the comment "In production
these come from interpreter/value.spl" — it tests a copy of the type checker
that lives inside the test file. Restoring it would add 33 green examples
coupled to nothing.

Passing the gate (example count held, failures rose):

| Spec | before | rename | fns renamed |
|---|---|---|---|
| `app/mcp_unit/mcp_completions_intensive_spec.spl` | 5 ex, 0 fail | 5 ex, **5 fail** | 38 |
| `app/mcp_unit/prompts_compiled_spec.spl` | 5 ex, 0 fail | 5 ex, **5 fail** | 38 |
| `lib/pure/nn/norm_spec.spl` | 27 ex, 0 fail | 27 ex, **27 fail** | 15 |
| `lib/pure/nn/pooling_spec.spl` | 31 ex, 0 fail | 31 ex, **20 fail** | 13 |
| `lib/pure/nn/pooling_integration_spec.spl` | 6 ex, 0 fail | 6 ex, **2 fail** | 11 |
| `lib/common/pure/nn/pooling_integration_spec.spl` | 6 ex, 0 fail | 6 ex, **2 fail** | 11 |
| `compiler/dependency/visibility_spec.spl` | 20 ex, 0 fail | 20 ex, **20 fail** | 3 |
| `compiler/di/di_runtime_spec.spl` | 12 ex, 0 fail | 12 ex, **12 fail** | 9 |
| `compiler/di/di_validation_spec.spl` | 10 ex, 0 fail | 10 ex, **10 fail** | 4 |

Failing the gate, NOT landed: `compiler/native/auto_vectorize_spec.spl` is the
one to note — 56 examples that stay 56/0 with all 8 functions in its module
renamed. It would have been the single largest green restore in this pass and it
proves nothing.

### `pending()` is invisible to the verdict line

The repo's own skip construct is not a way to record an honest non-pass.
`pending("never implemented")` prints `○ … (skipped)` and calls
`record_test_result(…, true, true)`, but it also does `BDD_COUNTS.0 += 1` and
never touches the failure counter. Measured directly:

    describe "PendingProbe":
        it "real pass":  expect(1).to_equal(1)
        pending("never implemented")
    -> 2 examples, 0 failures

So a machine reading the verdict cannot distinguish `pending` from a pass. Any
plan to convert this family to "explicitly pending" needs a runner change first,
or it re-creates the same false green under a nicer name.

### Landed this pass

9 specs, coupling-proven, plus their `test/unit` mirrors: **9 vacuous passing
examples -> 122 real passing examples**, all of which fail when the code they
name is renamed. No spec was landed on a green-restore alone.

### Still withheld, and why

- **17 specs** restore green with no production import — structurally uncoupled.
- **8 specs** restore green, import a real module, and survive the rename.
- **42 specs** now load with failures (385 + 459 examples, 246 failures between
  the two groups). These are honest reds, but each needs its own triage —
  production bug vs stale assertion vs never-implemented — before landing; the
  count-and-failure gate is fail-open when the examples already fail.
- **42 of the 69** still do not load: 22 name modules that do not exist, 5 fail
  to parse, the rest are misc.
- **44 gutted specs** recoverable only from a renamed directory, needing
  per-file confirmation that the recovered blob is the same spec.

## Fourth pass, 2026-08-06 — top of the "Remaining inventory" table, environment-gated variant

This pass worked the top of the `## Remaining inventory` table (highest
tautology counts first). It surfaced **two new sub-shapes** the earlier
passes hadn't named, and repaired the shape that was actually a false green.

### New shape 1 — whole-file stub, nothing to restore (NOT repaired)

`static_const_declarations_spec.spl` (53 tautologies) and
`alias_deprecated_spec.spl` (42) — the two highest-count files in the table —
are **not** the doc's canonical pattern (a stub replacing a commented-out real
body). Every `it` in both files was authored from the start as `val source =
"<snippet>"; expect(source.len()).to_be_greater_than(0)` — the snippet is
never fed to a lexer/parser/compiler. `grep -c '^\s*#.*expect('` is 0 in both;
`git log --follow` shows exactly one commit for each file (post-tree-wipe
squash), so there is no history to recover a real body from either. Sibling
`test/03_system/feature/usage/*_spec.spl` files (e.g.
`advanced_indexing_spec.spl`) show the repo's real pattern for this directory:
write actual Simple source directly in the `it` and assert on its *runtime*
behavior (`val arr = [10,20,30]; expect arr[-1] == 30`), not a string literal
whose length is checked. Repairing these two files means **authoring ~95 new
real test bodies** (including deciding how to assert "rejects duplicate
static declaration" — a parse-error case with no existing helper in this
directory) — that is feature-spec authoring, not a tautology fix, and is out
of scope for a bounded batch. Also hit and left unrepaired for the same
reason: `test/integration/doctest/discovery_spec.spl` +
`test/02_integration/doctest/discovery_spec.spl` (11 each — no
`discover_doctests`-shaped API exists anywhere in `src/`, so there is nothing
to couple to either) and `test/system/web_app_packaging_spec.spl` +
`test/03_system/infrastructure/web_app_packaging_spec.spl` (2 each — the two
tautology `it`s assert on locally-constructed strings, not a real
`SwaBuilder` call). **6 files reviewed, 0 repaired, all flagged
"needs feature-spec authoring, not a tautology fix."**

### New shape 2 — vacuous filler that does not gate anything (NOT repaired, deprioritized)

`llvm_parity_spec.spl` and `llvm_compiled_proof_spec.spl` (both copies each,
9 and 6 tautologies respectively) guard availability like this:

```
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module(...)          # <- runs UNCONDITIONALLY, no else
val result = compile_module_with_backend(...)
expect(result.is_ok()).to_equal(true)
```

There is no `else`, so the tautology never actually gates the real assertion
below it — the real code runs regardless of tool availability (confirmed:
`grep -n else:` finds exactly 0 matches in the touched regions of either
file). This is dead, misleading filler, but it is **not a false green** in
this family's sense: no coverage is hidden, and in an environment without
`llc`/`libLLVM` the real assertion would fail loudly, not pass silently.
(Likely provenance: the sibling `remote_riscv32_spec.spl` in the same batch
carries the comment "BUG-RT: skip() doesn't halt execution and return doesn't
work in it-lambdas. Guard entire test body with availability check" — these
two files look like an abandoned attempt at the same guard that forgot the
`else:`.) Fixing this properly (wrap the tail in `else:`, replace the filler
with `pending(reason)`) is mechanical but was deprioritized this pass in favor
of the shapes that are actual false greens; left unmodified and noted here so
the next pass doesn't have to re-derive the shape. `llvm_parity_spec.spl`
additionally carries `describe ..., tag: ["only-compiled"]`, which makes
`bin/simple test` report `0 examples, 0 failures` for the whole file under a
default invocation (tag-based filtering, unrelated to the tautology) —
flagged separately, not a tautology issue.

### Repaired: environment-gated tautology → honest `pending()` (4 base files, 8 physical files)

The remaining files in this pass's range had a genuine if/else gate — the
`pending_reason` tautology occupied the branch that fires when a required
external tool is *unavailable*, and real code occupied the other branch. That
is exactly the shape the repo's own `pending(name)` primitive exists for
(precedent already in the repo: `bcrypt_kat_spec.spl`,
`argon2id_rfc9106_kat_spec.spl` call `pending("...")` from inside a
conditional `it` body). Fix applied uniformly: replace
`val pending_reason = "..."; expect(pending_reason.len()).to_be_greater_than(0)`
with `pending("...")` in the branch that previously held the tautology;
the branch with real code was left untouched byte-for-byte.

| Spec (+ mirror) | tautologies fixed | shape |
|---|---|---|
| `test/01_unit/os/crypto/ffdhe_kat_spec.spl` + `test/unit/os/crypto/ffdhe_kat_spec.spl` (byte-identical before edit) | 2 each | unconditional (`@slow`, no if/else — 2048-bit modexp is O(minutes) in the interpreter, a documented, genuine deferral) |
| `test/02_integration/compiler/llvm_backend_e2e_spec.spl` + `test/integration/compiler/llvm_backend_e2e_spec.spl` (byte-identical before edit) | 4 each | if(unavailable)=tautology / else(available)=real |
| `test/02_integration/compiler/llvm_native_link_spec.spl` + `test/integration/compiler/llvm_native_link_spec.spl` (**not** byte-identical — the `02_integration` copy carries one extra `it "keeps normal runtime owners..."` the other copy lacks; treated independently, same edits applied to the shared region) | 5 / 4 | mixed polarity: 2 occurrences are if(available)=real / else(unavailable)=tautology, the rest are if(unavailable)=tautology / else(available)=real |
| `test/02_integration/baremetal/remote_riscv32_spec.spl` + `test/integration/baremetal/remote_riscv32_spec.spl` (**not** byte-identical — the `test/integration` copy carries `tag: ["only-compiled"]` on every `describe`, the `02_integration` copy does not; the touched `if/else` bodies themselves are identical text, confirmed via `diff` on the region) | 3 each | if(available)=real / else(unavailable)=tautology |

**Verification (this sandbox has llc, libLLVM-18/20, qemu-system-riscv32,
gdb-multiarch, riscv64-linux-gnu-gcc, riscv64-unknown-elf-gcc, and a C
compiler all installed), so every "available" branch was already the one
executing before this edit — the fix only changes the never-taken branch's
text in this environment, which is exactly why example/failure counts are
unchanged by the edit itself:**

- `ffdhe_kat_spec.spl` (both copies): `14 total` before and after,
  `0 failures` before and after. After the edit the two deferred examples
  print `○ 2048-bit modexp is O(minutes)... (skipped)` instead of a bare `✓`
  — the reason is now visible and grep-able instead of hidden behind a
  tautology that reads identically to a real pass.
- `llvm_backend_e2e_spec.spl` (both copies): `26 total, 24 passed, 2 failed`
  after the edit, identical on both copies. Both failures are **pre-existing
  and unrelated to this edit** — `✗ finds llc binary` (`expected
  /usr/bin/llc-20 to start with llc`, i.e. `to_start_with("llc")` against a
  full path) lives in the untouched `else:` branch, and `✗ creates
  compatibility backend` (`expected x86-64-v1 to equal x86-64`) is in an
  unrelated `describe` block this pass never touched. Left as-is per scope
  (no product-bug fixing in this pass).
- `llvm_native_link_spec.spl`: `02_integration` copy `6 total, 4 passed, 2
  failed`; `integration` copy (missing the extra test) `5 total, 4 passed, 1
  failed`. The shared failure, `✗ links a native executable when
  prerequisites are present` (`expected false to equal true`, i.e.
  `link_llvm_native(...).is_ok()` is false), is in the untouched `else:`
  branch — pre-existing, unrelated to the edit. The `02_integration`-only
  failure (`✗ keeps normal runtime owners when bootstrap links native_all`)
  is in a describe block with no tautology at all — also pre-existing,
  unrelated.
- `remote_riscv32_spec.spl`, `02_integration` copy: `85 total, 78 passed, 7
  failed`. All 3 edited QEMU-gated examples pass green with no `○` marker
  (confirming the real `if`-branch, not the edited `else`, is what ran); the
  7 failures are all in unrelated `GDB MI Parser` / `DebugError` describe
  blocks this pass never touched. `test/integration` copy: `1 total, 0
  passed, 1 failed`, every describe reporting `0 examples, 0 failures` — this
  is the pre-existing `tag: ["only-compiled"]` filtering every example out
  under a default `bin/simple test` invocation (see New shape 2 note above);
  the file content in the touched region is confirmed identical to the
  working `02_integration` copy, so this is a filtering artifact, not a
  regression from this edit.

No coupling gate or sabotage-proof was run for this batch: unlike the
class-(i)/(ii) restores in prior passes, none of these edits newly exercise
production code — the "available" branch (the one with real assertions) was
already executing, before and after, in every environment where the tool in
question is present. The repair is scoped to making the *unavailable* path
honest instead of silently green; that claim is verified by before/after
example-count and failure-count equality (or, for `ffdhe_kat_spec.spl`, by
the transcript now showing `○ ... (skipped)` for the deferred cases). Sibling
`bcrypt_kat_spec.spl` / `argon2id_rfc9106_kat_spec.spl` are the existing
sabotage-independent precedent for this exact `pending(reason)`-inside-`it`
idiom.

### Net effect and updated inventory

**9 tautology occurrences converted to honest `pending()` across 4 base
files / 8 physical files** (`ffdhe_kat_spec.spl` ×2 files ×2 occurrences,
`llvm_backend_e2e_spec.spl` ×2 files ×4, `llvm_native_link_spec.spl` ×2 files
×5/4, `remote_riscv32_spec.spl` ×2 files ×3). These 8 files are removed from
the `## Remaining inventory` table above. `static_const_declarations_spec.spl`,
`alias_deprecated_spec.spl`, both `discovery_spec.spl` copies, and both
`web_app_packaging_spec.spl` copies remain in the table (not repaired — see
New shape 1). `llvm_parity_spec.spl` and `llvm_compiled_proof_spec.spl` (both
copies each) also remain in the table (not repaired — see New shape 2).
18 files were reviewed this pass in total.

**Re-verified 2026-08-10: this landed.** All 8 physical files (`ffdhe_kat_spec.spl`
×2, `llvm_backend_e2e_spec.spl` ×2, `llvm_native_link_spec.spl` ×2,
`remote_riscv32_spec.spl` ×2) show `git diff origin/main -- <path>` = empty and
`grep -c pending_reason` = 0, `grep -c "pending("` >= 2 on `origin/main` as of this
date — the repair described above is present on `main`, not just in a stale
working copy.
- **7 gutted specs** with no recoverable content anywhere.
