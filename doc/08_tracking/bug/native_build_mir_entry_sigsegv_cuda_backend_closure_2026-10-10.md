# native-build SIGSEGV entering MIR lowering on the CUDA backend closure (exit 139)

- **Date:** found 2026-10-10. Filed as its own record 2026-11-22, because until
  then it was tracked only inside `cuda_optimizer_surface_owner_2026_10_10.md`.
- **Status:** open, reproducibility untested. A current producer has not reached
  this point: the 2026-11-22 runs stopped earlier, from OOM at MIR 200/514 under
  8G and from SIGSEGV at HIR 82/514 under 20G.
- **Severity:** P2. Blocks a native object for `src/plugins/backend_cuda/cuda_backend.spl`.

## Original evidence (2026-10-10, recorded in cuda_optimizer_surface_owner_2026_10_10.md)

- Producer: an unadmitted pure-Simple explicit-call-types diagnostic candidate,
  sha256 `72b495b3f2cbb72b3a1f8c6bf01e7962a4d38fda17d905a2c7a0e004c066c6a5`.
- Recipe: `native-build --source src/compiler --source src/app --source src/lib
  --source src/plugins/backend_cuda --source src/compositions/kernel_llvm_cranelift
  --entry-closure --entry src/plugins/backend_cuda/cuda_backend.spl --threads 10`
  with `SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
- HIR 157/157 passed. Monomorphization: 2 generic functions, 24 calls,
  9 specializations, 0 unresolved.
- Then the worker died with SIGSEGV (exit 139, build exit 117) during MIR
  lowering, and no binary was produced.
- An independent SMF path (producer sha256 `8288ec48e1ee0ef9...`) failed the same
  way: SIGSEGV entering MIR lowering.

## Next step
Re-run the recipe on a current producer, without the 8G cap and without the
20G HIR crash (`native_build_hir_sigsegv_under_20g_cgroup_cuda_port_closure_2026-11-22`),
and see whether MIR entry still crashes. If it does, take a backtrace.
