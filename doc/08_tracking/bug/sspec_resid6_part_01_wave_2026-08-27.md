# sspec modernization residual wave resid6_part_01 — blocked and pre-existing-red specs

- Date: 2026-08-27
- Batch: /tmp/sspec_census/resid6_part_01 (52 specs, all re-scored fresh after
  clearing `.simple/cache/sspec-maintain`). All started at effective 49
  (blocker cap); fixes listed below raised 12 specs above 80 with mirror
  regeneration and dual checks (green / injected-bug FAIL / green).

## Modernized (score 49 -> >80)

- aggregator_walker 93, aggregator_compose 93, template_kind_can_follow 95,
  shb_import_test 97, host_cpu_variant 93, fsync 93,
  .spipe_wrapped_entry_native_byte_io 91, _throwaway_broker 93,
  _throwaway_import 93, js_vm_reclamation 84, ml/tracking/run_spec 90,
  .spipe_wrapped_entry_task_spawn 96 (score only; run blocked, see below).
  Common fixes: `"""## Purpose and audience"""` docstring (NAR-001), one or
  more real `expect(...)` oracles replacing receiver-style/vacuous forms
  (ORA-001/ORA-002), `# @req` placement (TRC-003), mirror regen (MNT-002).

## Source-grep guard specs (ORA-002 by design — blocked)

Same class as
`source_grep_guard_specs_blocked_on_selfhosted_binary_2026-08-26.md`, extended
to `src/compiler/**`, `src/lib/**` and `scripts/**` pins: every asserting
scenario reads source text (`file_read`/`rt_file_read_text`/`read_file`/
`read_text`) and asserts `.contains(...)` on implementation shapes (import
hygiene, comment contracts, extern declarations). A behavioral oracle would
assert different code than the contract pinned, so they are left as-is until a
self-hosted binary allows invoking the real pure-Simple CLI/module paths:

driver_memory_lifecycle_family, leak_check_owner_imports,
flat_ast_inline_asm_bridge, hir_module_callable_index,
hir_stmt_dispatch_source, module_surface_index_alignment,
pattern_condition_mutability_source, symbol_table_dict_get_source,
tuple_destructure_mutability_source, interpreter_aop_weave, script_language,
bootstrap_binary_lowering_source, option_text_unwrap_pointer,
unresolved_method_fatal_guard_source, resolve_nil_guard,
rewriter_atomic_write_contract, vulkan_cross_fail_closed, font_renderer,
backend_rocm_renderbackend, engine_vulkan_font_route,
ffi_out_param_via_return_value_detection, watchdog_manager,
connection_heartbeat_numeric_guard, kms_vendor_adapters,
session_int_numeric_guard, arm64_payload_symbol_contract (26).

## Pre-existing red at HEAD (verified via `git show HEAD:<spec>` restore; left RED)

- `lib/common/js/engine/js_vm_reclamation_spec.spl` — `Results: 4 total, 1
  passed, 3 failed` on untouched HEAD copy. Modernization landed; score 84.
- `lib/std/ml/tracking/run_spec.spl` — `error: runtime: Module "std.ml" does
  not export 'tracking'` on HEAD copy. Modernization landed; score 90.
- `compiler/native/build_native_min_spec.spl` — `semantic: Cannot resolve
  module: linker`, 0 examples executed. Untouched.
- `lib/std/parser/error_recovery_spec.spl` — `error[E1002]: function 'feature'
  not found`, 0 examples executed. Untouched. (Also uses unrecognized
  `should_equal` matchers.)
- `lib/std/language/mixin_static_poly_integration_spec.spl` — bare `expect true`
  at describe level; runner reports zero examples executed, rc=1. Untouched.
- `multi_mode_test_runner_spec.spl` — `semantic: variable 'TestExecutionMode'
  not found`, 34/34 fail. Untouched.
- `compiler/vhdl_{riscv_gap,subprogram,testbench}_spec.spl` — main()-style
  print specs, `no examples executed`, rc=1. Untouched.
- `lib/nogc_async_mut/.spipe_wrapped_entry_task_spawn_runtime_pool_spec.spl` —
  untracked at HEAD; `semantic: function 'task_spawn' not found` on the seed
  binary. Modernization landed (score 96); run blocked on self-hosted binary.

## Blocked on other grounds

- `gpu/render_2d_riscv_spec.spl` — print-only diagnostics, no executed
  assertion; needs riscv32/64 cross-target JIT + GPU hardware.
- `compiler/mir/mir_opt_benchmark_spec.spl` — every scenario is a `pass`
  scaffold; real MIR optimization benchmarks require the self-hosted MIR
  pipeline.
- `compiler/r2_pending_helper_spec.spl` — deliberate r2 pending/fail-probe
  family member (ORA-001 "pending or fail-fast scaffold" is its purpose);
  currently green with 1 skipped.

## Delete candidates (vacuous scaffolds)

- `compiler/frontend/ast_types_spec.spl` — 8 lines, zero content past the
  header comments.
- `lib/nogc_async_mut/ml/engine_spec.spl` — single `skip` placeholder.
- `compiler/parser/desugaring_spec.spl` — 23 scenarios, every one
  `expect(1).to_equal(1)`.
- `compiler/parser/parser_actor_spec.spl` — 16 scenarios, every one
  `expect(1).to_equal(1)`.
- `lib/std/language/mixin_static_poly_integration_spec.spl` — 8 describes of
  bare `expect true`, zero examples execute.
