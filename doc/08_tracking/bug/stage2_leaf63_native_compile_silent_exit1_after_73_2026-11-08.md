# Frozen stage2: native_compile exits 1 silently after 73/289 modules (leaf 63)

- **Severity:** P1 (blocks phase-3 leaf 63 and the vb_mm1 fold)
- **Status:** open
- **Host:** Windows x86_64, llvm-mingw
- **Found:** 2026-11-08

## Symptom
The frozen `C:/dev/p3new/stage2.exe` builds the leaf-63 closure (`fable_leaf63c.ps1`: `native-build --entry-closure --go-to-end --emit-object`, cache `combined3`). It fails the same way on every run:
- MIR shards finish clean: `claimed=289 passed=289 sealed_failed=0 failed_modules=0`.
- The parent then codegens the modules one at a time and exits rc=1 after `done=73 total=289`. The last module it reports is `compiler.frontend.join_point_attr_registry`.
- No error is printed. The native-build stderr is truncated, and `objs=0`.

This is reproducible: run 2 and run 3 stopped at the identical point. Nothing from the earlier runs was reused (`cached=0`, 216 uncached each time), so the stop is not a memory-cap kill. The cap was 60 GB and the peak was 52 GB.

The MIR shard worker measured a peak commit of 55 GB against a 34 GB static estimate.

## Next
- Find module 74 in parent codegen order.
- Compile it alone with stage2 to get the real error.
- Check why the objects from modules 1-73 are not cached across runs.

## Evidence
Local logs: `C:/dev/p3new/cgprobe/fable_leaf63c_run2/`, `C:/dev/p3new/cgprobe/fable_leaf63c/`.

Related: `s3_selfbuild_stale_surface_index_impls_backend_2026-11-07` (the self-built path is also blocked).
