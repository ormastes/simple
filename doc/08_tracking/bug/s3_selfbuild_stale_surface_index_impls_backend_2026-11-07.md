# Stage-3 self-build: stale surface index [impls] in backend modules

- **Severity:** P1 (blocks phase-3 self-bootstrap: stage3 building stage3)
- **Status:** fix-implemented-verification-pending (see Fix 2026-11-13)
- **Host:** Windows x86_64, llvm-mingw
- **Found:** 2026-11-07, leaf 63

## Symptom
`s3_fable61.exe` was used as the compiler to build the leaf-63 closure (vb_mm1 fold plus leaf-62 folds, `native-build --entry-closure --go-to-end`). It failed in HIR with 281 failures. These were real HIR failures:

```
stale surface index [impls]: module=compiler.backend.common.type_mapper surface_key=1 1008 owner=LlvmTypeMapper position=3 live_len=0; the memoized index outlived the surface rows it indexes
stale surface index [impls]: module=compiler.backend.codegen_types surface_key=1 180 owner=VhdlBackend position=2 live_len=1
```

- **Root failures:** `compiler.backend.{_MirToLlvm.*, mir_to_llvm, llvm_codegen_adapter}` and `plugins.backend_vhdl.*`.
- **Downstream:** 232 non-plugin `hir_dependency` failures.

The same closure built by the frozen `stage2.exe` does not hit this. That is the leaf-62 path.

## Analysis
The diagnostic is `hir_stale_surface_index_message` in `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`. A memoized impl position outlives the impl rows of a surface. `live_len=0` means the rows were released or reset while the memo stayed alive. The failure is native-only and only appears in the self-built compiler. Suspects:
- surface impl arrays freed by transient-scope teardown (#7506 deferred-release changes in leaf 61);
- native array reassignment not preserving the memo/backing identity.

## Repro
`C:/dev/p3new/cgprobe/fable_leaf63.ps1` (`-Exe s3_fable61.exe`, entry `leaf63_entry/main.spl`). The log is kept at `C:/dev/p3new/s3new/leaf63_selfbuild_stale_surface.log`.

## Workaround
Build leaf 63 with the frozen stage2 (`fable_leaf63b.ps1`).

## Fix (2026-11-13)
- **Status:** fix-implemented-verification-pending (native stage3 self-build re-run pending).
- Fix on `origin/release/1.0.0`: `9106a316ad1` (`HirLowering.invalidate_impl_index` at the driver
  surface teardown + fail-closed length guards) and `ce2088532d3` (STALESURF: `ensure_impl_index`
  keys the memo by `{generation} {physical_index} {impls.len()}`, so a shrunk/replaced impls array
  re-indexes its live rows and a stale position is unreachable).
- Regression: `bin/simple test test/01_unit/compiler/hir/impl_index_staleness_guard_spec.spl`
  -> `outcome=OK executed=6 passed=6 failed=0` (seed, 2026-11-13).
- Still open for the owner: the length key removes the stale-index crash, but if a live surface's
  impls rows really are released early (`live_len=0` while still imported), the importer now sees
  zero impls instead of an error. Confirm with the leaf-63 self-build (`fable_leaf63.ps1 -Exe
  <new s3>`) that no `unknown method` failures replace the 281 HIR failures.
