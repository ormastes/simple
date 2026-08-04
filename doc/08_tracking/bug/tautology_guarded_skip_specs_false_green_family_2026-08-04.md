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
| test/integration/compiler/llvm_native_link_spec.spl | 5 |
| test/02_integration/compiler/llvm_native_link_spec.spl | 5 |
| test/integration/compiler/llvm_backend_e2e_spec.spl | 4 |
| test/02_integration/compiler/llvm_backend_e2e_spec.spl | 4 |
| test/integration/baremetal/remote_riscv32_spec.spl | 3 |
| test/02_integration/baremetal/remote_riscv32_spec.spl | 3 |
| test/unit/os/crypto/ffdhe_kat_spec.spl | 2 |
| test/system/web_app_packaging_spec.spl | 2 |
| test/03_system/infrastructure/web_app_packaging_spec.spl | 2 |
| test/01_unit/os/crypto/ffdhe_kat_spec.spl | 2 |
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
