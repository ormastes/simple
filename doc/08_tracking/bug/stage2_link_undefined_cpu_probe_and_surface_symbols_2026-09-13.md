# Site 17: Stage 2 fails to LINK — 6 undefined symbols on aarch64-apple-darwin

- **Status:** OPEN (2026-09-13). Blocks the macOS Stage-2 lane before any
  post-build gate is reached.
- **Lane:** `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
  virgin root, worktree `agent-a48e6e7adea865a52`, run 30, tip `6c801a7f309`
  (carrying PR #843).
- **Not caused by, and not related to, site 16.** Site 16's gate sits at
  `bootstrap-from-scratch.sh:3291`, inside `if [ "${stage2_status}" -eq 0 ]`.
  This failure sets `stage2_status=1`, so that gate is never reached.

## Verbatim

```
  diagnosis: 2 diagnostic line(s) found. First 5:
    | Build failed: link failed: ld: warning: -ld_classic is deprecated and will be removed in a future release
    | clang++: error: linker command failed with exit code 1 (use -v to see invocation)
PASS — 1 check(s), stage stage2 failed (exit 1) and said why
  warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

The real cause is in the build log, not the summary
(`.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log:2734-2748`):

```
Undefined symbols for architecture arm64:
  "__sffi_enum_discriminant", referenced from:
      _compiler__mir___MirLoweringExpr__method_calls_literals__MirLowering.mir_type_is_scalar_numeric in libspl_objects.a(mod_348.o)
     (maybe you meant: _compiler__mir___MirLoweringExpr__expr_dispatch___sffi_enum_discriminant, ...)
  "_module_surfaces_promote_reason", referenced from:
      _compiler__driver__driver_source_pipeline_parsing__CompilerDriver.parse_all_streaming_surfaces_in_place_impl in libspl_objects.a(mod_657.o)
  "_rt_cpu_is_aarch64" / "_rt_cpu_is_riscv64" / "_rt_cpu_is_x86_64" / "_rt_cpuid", referenced from:
      _compiler__types__simd_capabilities__detect_capabilities in libspl_objects.a(mod_278.o)
      _compiler__types__simd_capabilities__detect_x86_capabilities in libspl_objects.a(mod_278.o)
ld: symbol(s) not found for architecture arm64
```

## Three distinct classes, not one defect

1. **`rt_cpu_is_*` / `rt_cpuid`** — declared `extern fn` in
   `src/compiler/types/simd_capabilities.spl:23,56` and DEFINED in
   `src/runtime/runtime_native.c:15033,15075`. The lane links
   `--runtime-bundle core-c-bootstrap`, so the definitions are present in the
   tree but not in the bundle this stage links. Either the bundle's source list
   must carry them or the compiler must not reference them on this lane.
2. **`module_surfaces_promote_reason`** — re-exported through `export use` at
   `src/compiler/20.hir/hir_lowering/module_surface.spl:5` and called at
   `src/compiler/80.driver/driver_source_pipeline_parsing.spl:585`; no
   definition reaches the link. Related, possibly the same root as
   `doc/08_tracking/bug/stage2_sanity_module_surface_registry_promotion_fails_2026-09-13.md`.
3. **`__sffi_enum_discriminant`** — a per-module SFFI helper. The linker's own
   "maybe you meant" list shows FOUR sibling modules each emitting their own
   mangled copy (`..._expr_dispatch___sffi_enum_discriminant`, etc.) while
   `method_calls_literals` references the UNMANGLED name. A per-module helper
   emission/mangling gap, not a missing runtime symbol.

## Why this is new

Run 29 (2026-09-13, earlier tip) built and linked Stage 2 cleanly and reached
the site-16 manifest gate. This is therefore a regression introduced between
run 29's tip and `6c801a7f309`, not a standing condition. Bisecting the culprit
commits over `src/compiler/types/simd_capabilities.spl`,
`src/compiler/20.hir/hir_lowering/`, `src/compiler/50.mir/` and `src/runtime/`
is the next step and has NOT been done here.
