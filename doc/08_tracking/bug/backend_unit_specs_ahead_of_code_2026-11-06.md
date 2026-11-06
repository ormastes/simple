# Backend unit specs that fail for reasons a spec edit cannot fix (2026-11-06)

Branch: `release/1.0.0`. Runner: Rust seed `release100-7a0e6fe516f-20261031`,
macOS arm64, `bin/simple test <spec>` one file at a time.

These failures stayed open after the 2026-11-06 sweep of
`test/01_unit/compiler/backend/`. They are **not** stale expectations: the code
the spec describes was never written or never landed on this line.

| Spec | Result | Cause |
|---|---|---|
| `actor_runtime_abi_contract_spec` | 0/1 | The spec was written before the code. `rt_actor_spawn` (Rust runtime `value/actors.rs`) calls the body as `f(std::ptr::null())`, so the `ctx` argument is dropped, and it expects `Option<extern "C" fn(RuntimeValue)>` / `f(callback_ctx)`. The LLVM emitter `emit_actor_spawn` (`codegen/llvm/emitter.rs`) calls `rt_actor_spawn` with ONE argument (the block id), but `runtime_sffi.rs:993` declares `[I64, I64]`. That is an ABI mismatch. Neither fix exists on any ref (`git log --all -G`). A fail-closed emitter patch compiled with `cargo check --features llvm`, but on its own it does not make the spec pass, so it was not landed. |
| `armv7_cortex_a9_target_spec` | 0/2 | `llvm_arm_baremetal_config_for` (Cortex-A9 soft-float profile) does not exist on any branch. `llvm_target.spl` only has `llvm_arm32_baremetal_arch` / `_environment`. This needs the feature built. |
| `jit_typed_ir_equivalence_spec`, `jit_typed_ir_reject_spec` | 0/1 each | `compiler.backend.jit_typed_ir` exists only on the unmerged ref `02a9a48d7f5` (`src/compiler/70.backend/jit_typed_ir.spl`). The specs landed without the module. |
| `combinational_composition_to_vhdl_spec` | 0/1 | `compiler.mir.hwir.combinational_composition` and `backend/combinational_composition_to_vhdl.spl` exist only on `origin/chore/merge-share-history` (`a8244005f9b`). They never reached release/1.0.0. |
| `group_native_thread_capability_spec` | 1/2 | This spec is tagged `only-compiled`. The seed interpreter's `rt_thread_spawn_isolated_with_args` requires a closure as its first argument, so the threaded case can only run in compiled mode. |

## Related: the `app.spipe.testing` alias does not exist

`app.spipe.testing` has never existed on any ref. `demand_backend_promotion_spec`
was fixed by importing `std.spec.*`. Seven other specs outside the backend
directory still import it and fail at module resolution:
`test/02_integration/compiler/demand_compile_observability_integration_spec.spl`,
`test/02_integration/compiler/cache/reverse_reference_projection_receipt_spec.spl`,
`test/05_perf/compiler/demand_compile_pipeline_perf_spec.spl`,
`test/01_unit/compiler/cache/package_scc_scheduler_spec.spl`,
`test/01_unit/compiler/hir/hir_demand_set_spec.spl`,
`test/01_unit/compiler/perf/demand_compile_counters_spec.spl`,
`test/01_unit/compiler/mir/demand_mir_integration_spec.spl`.

## Related: sync clobber `0a749ba7f10`

`0a749ba7f10` ("chore(sync): session work products ... fixes preserved at origin
versions") rewound 207 `src/` files (-10,830 lines). One example:
`backend/compiler.spl` lost the `CraneliftTarget` AOT routing added in
`3b7622ac01b`, and this sweep restored it. Other rewound hunks can still be
present outside the backend specs.
