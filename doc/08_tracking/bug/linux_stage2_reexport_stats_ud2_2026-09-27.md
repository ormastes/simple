# Linux Stage2 re-export statistics trap

Status: both observed bare-return sites changed in source; the second change
is unverified by a rebuilt diagnostic binary, 2026-09-27.

The admitted Stage2 bootstrap compiler trapped with `SIGILL` while compiling
`build/collection-planner-scalar-probe.spl`. GDB placed the trap at
`HirLowering.report_reexport_chase_stats`, called through
`find_reexport_source_walk` during HIR import registration. The method in
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`
used two bare early `return` statements. This matches the earlier native
bootstrap lowering fault where a bare return inside a `me` method emitted
`ud2`. The method now uses nested conditions, preserving its 20,000-call
reporting interval and environment gate without an early return.

The scalar probe has not reached DataFrame execution. Bootstrap-only seed
diagnostic rebuilds ran in the isolated WSL checkout at
`/home/ormastes/simple-collection-planner-shared`. Their binaries are not
admitted compilers or production test runners.

The first diagnostic rebuild completed (`896 compiled, 0 failed`), but a probe
invocation was refused by `PLUG-E-K1-POLICY` before HIR work: the ad-hoc build
omitted the canonical `src/compositions/kernel_llvm_cranelift` source. The
composition file hash matches the prior bootstrap transcript. A corrected
diagnostic rebuild with that source and `SIMPLE_KERNEL_K1_POLICY=llvm-cranelift`
completed (`902 compiled, 0 failed`) in
`build/collection-planner-hir-guard-k1-build.log`. Its focused DataFrame probe
still trapped before reaching DataFrame code. GDB now places `SIGILL` at
`HirLowering.materialize_imported_field_dependency_inner`, through the glob
import materialization path; the earlier
`report_reexport_chase_stats` frame is absent. That method contained bare
early returns for invalid/stale surface indices and already resolved type
dependencies. Its control flow now uses guarded branches with the same lookup
order and error behavior, without bare returns. `objdump` of the trapped
diagnostic binary shows three consecutive `ud2` instructions at `0x6c496e`,
`0x6c4970` and `0x6c4972` immediately after the method's return epilogue;
GDB stopped on the middle one. This supports the bare-return lowering
hypothesis, but a rebuilt run is still needed to prove it. The run emitted
unresolved re-export receipts for `text` and `i64` from
`lib.nogc_async_mut.df.mod`, which may be a
separate import issue. This was the third focused verify/fix cycle in this
session, so no further rebuild or probe retry was made after the source edit.
The next session should test the corrected source, separate any remaining
`ud2` lowering fault from genuine unresolved imports, then run the canonical
admission and full matrix gates.
