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

## Origins, found by symbol archaeology rather than a range bisect (2026-09-13)

The chain doc never records run 29's tip sha, so the range could not be bisected.
`git log -S<symbol>` is stronger evidence anyway and names a commit per class.

### Class 2 — `module_surfaces_promote_reason`: a stale-base clobber

`6a49e75efe0` ("diag(compiler): name the surface, field and scope in a phase-2
promotion failure") ADDED `module_surfaces_promote_reason`, the
`module_surface_promote_field(s)` helpers and `module_surface_promote_scope_sentinel`,
made `module_surfaces_promote` a wrapper over it, and pointed the driver at it.

`db127a8e8c4` ("fix(hir): stop module surface promotion failing on an
already-persistent field") then rewrote `module_surfaces_promote` from a base
that PREDATED `6a49e75efe0`. Its own fix is correct — the per-field check must
be the sibling's post-condition (a SECOND promote reports true only for a value
still owned by the dying scope), not the first promote's result — but the
rewrite deleted `module_surfaces_promote_reason` outright. The `export use`
facade (`module_surface.spl:5`) and the driver call
(`driver_source_pipeline_parsing.spl:33,585`) were left pointing at a symbol
with no definition anywhere in `src/`, which is exactly what the linker said.

**Fix is a merge, not a restore.** `module_surfaces_promote_reason` is
reinstated with `db127a8e8c4`'s post-condition inside
`module_surface_promote_field`, so the 19,512-chance false abort that commit
killed stays killed while every failure route names the field, the surface index,
its logical/canonical/package names and the scope sentinel again.
`module_surfaces_promote` is once more `module_surfaces_promote_reason(...) == ""`.

The spec `test/01_unit/compiler/hir/module_surface_promote_reason_spec.spl`
survived and had NOT been updated for `db127a8e8c4`'s contract change: its two
behavioural examples assert `reason == ""` / `promoted == true`, which the Rust
seed's always-true `rt_transient_heap_promote` stub makes unsatisfiable under the
new post-condition. Measured on unmodified `origin/main`, `module_surfaces_promote`
already answered **false** for that same registry, so those two examples were
already red before this change. They now assert what IS decidable under the stub
— the verdict is never an unnamed bare failure, and the bool wrapper is exactly
`reason == ""` — instead of asserting the stub. 4 examples / 0 failures.

### Class 3 — `__sffi_enum_discriminant`: a seed name-resolution defect

Introduced by `d5b5d9f3408` ("fix(mir): Dict.remove returns the removed VALUE
natively"), which added `MirLowering.mir_type_is_scalar_numeric` to
`method_calls_literals.spl` with ten `_sffi_enum_discriminant` call sites. That
file defines no such helper; it glob-imports `expr_dispatch.*` and
`switch_operators_calls.*`, each of which defines its own PRIVATE copy. Neither
is exported, so the name should not resolve at all — the seed resolved it anyway
and emitted an UNMANGLED external call. The interpreter is permissive here, so
nothing before a native link could catch it.

Worked around by defining `_sffi_enum_discriminant` locally in
`method_calls_literals.spl`, the shape its three sibling modules already use,
delegating to the file's existing `_sffi_method_hir_type_discriminant` wrapper so
no new direct `rt_*` call site is added. The seed defect is filed separately:
`doc/08_tracking/bug/glob_imported_private_fn_lowers_to_unmangled_extern_2026-09-13.md`.

A sweep confirms `method_calls_literals.spl` was the only file in the tree
referencing `_sffi_enum_discriminant` without defining it.

### Class 1 — `rt_cpu_is_*` / `rt_cpuid`: owned elsewhere

Covered by PR #846, which twins `rt_cpuid` and the three arch gates into the Rust
runtime crate. Note the discrepancy for whoever picks this up: this record says
the lane links `--runtime-bundle core-c-bootstrap` (so `runtime_native.c`'s
definitions at 15033/15067/15075/15083 should be present), while #846 and
`src/compiler_rust/runtime/build.rs:372` ("Narrow Stage2 provider:
runtime.c/runtime_native.c cannot be linked") say the Rust crate is the provider.
Not chased here.

### Verification tier reached

Interpreter tier only. A native link probe against the local seed
(`src/compiler_rust/target/bootstrap/simple`, dated 2026-09-05) cannot reach the
link stage at all — it fails first with `error: semantic: unknown extern function:
rt_env_vars`, i.e. the local seed predates the tip. The deciding check is the
Stage-2 lane itself, which builds its own seed.
