# Stage-3 self-build: stale surface index [impls] in backend modules

- **Severity:** P1 (blocks phase-3 self-bootstrap: stage3 building stage3)
- **Status:** open
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
