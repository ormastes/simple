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

## Fix (2026-11-08) — fix-implemented, verification pending

Root cause: `ensure_impl_index` memoized impl positions under the key
`{generation} {physical_index}` only. In the stage-3 self-build the same key
was later presented with a surface whose `impls` array had a different length
(live_len 0/1 vs memo positions 2/3) — either released transient rows or a
different surface array instance — so the memo applied positions to an array
it was never built over.

Fix: the key now also carries `imported_mod.impls.len()`
(`module_reexport_materialization.spl`), so a shrunk/replaced array misses the
memo and is re-indexed against its live rows; a stale position is unreachable.
The IMPLIDX-GUARD diagnostic stays as defense in depth.

Specs: `test/01_unit/compiler/hir/impl_index_staleness_guard_spec.spl` —
before 4/6 (shrunk + emptied surface repros failed), after 6/6.

Unverified: native s3 self-build. If the surface rows are genuinely lost
(live_len=0 where impls must exist), methods will now be absent rather than
fatal; that would indicate the ModuleSurface impl arrays are not promoted out
of the transient scope and needs a follow-up.
