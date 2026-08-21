# `unresolved type: CodegenTarget` in driver_public_api.spl — bare `export Name` re-export route is unresolvable

- **Filed:** 2026-08-21
- **Status:** fix implemented (`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`); behavioural verification BLOCKED, see below
- **Symptom (stage1 run6, tree `5020e8f3f45`):**

```
[hir-fatal] source_idx=7 path=src/compiler/driver/driver_public_api.spl error_idx=0
  text=HIR lowering error in src/compiler/driver/driver_public_api.spl: unresolved type: CodegenTarget
[hir-fatal] source_idx=8 path=src/compiler/driver/driver_public_compile.spl
  text=HIR lowering error in src/compiler/driver/driver_public_compile.spl: unresolved type: CodegenTarget
```

## Why it looked impossible

`src/compiler/80.driver/driver_public_api.spl` is THREE lines — two `pub use`
re-exports and a comment. It never names `CodegenTarget`, and neither does any
module in its import closure: a breadth-first walk of that closure visits
exactly 10 modules

```
src/compiler/80.driver/driver_public_api.spl
src/compiler/80.driver/driver_public_{shared,header_parse,headers,interpret_bridge}.spl
src/compiler/00.common/driver_{core_types,core_modes,compile_options,compile_result,source_file}.spl
```

and `grep -c CodegenTarget` over all ten is **0**. `driver_public_compile.spl`,
the second offender, is the same shape: a pure `pub use` facade. The error is
attributed by `HirLowering.module_filename` (`hir_lowering/types.spl:380`), so
the attribution is real — that module's lowering genuinely emitted it.

The route is a re-export the surface builder cannot record.

## Root cause

`module_surface_registry_index.spl:288-291` builds the export routes. For a
**non-glob** export item it pushes:

```
export_route_target_indices = export_route_target_indices.push(-1)
export_route_target_names   = export_route_target_names.push("")
```

i.e. a bare `export Name` records **no source module at all**. Only the
`export ...*` glob branch resolves and stores a target index.

`find_reexport_source_walk` (`_Items/module_reexport_materialization.spl:133+`)
then has exactly two ways to follow a non-glob route:

1. the facade DECLARES `exp_source` itself, or
2. the route is ALIASED (`export src:local`, so `exp_source != wanted`) and it
   recurses on `exp_source`.

A bare `export CodegenTarget` in a package `__init__.spl` satisfies neither —
the facade declares nothing and `exp_source == wanted` — so the walk falls out
of the loop and returns `found: false`. The silent not-found then resurfaces
much later as the hard, non-recovered `unresolved type: {name}`
(`hir_lowering/types.spl:815`), blamed on whichever module was being lowered.

The offending facades are real and in the CodegenTarget route:

```
src/compiler/70.backend/backend/__init__.spl:7   export BackendKind, CodegenTarget, OptimizationLevel, BuildMode
src/compiler/70.backend/backend/__init__.spl:42  export BackendKind, CodegenTarget, OptimizationLevel, BuildMode
src/compiler/10.frontend/core/__init__.spl:340   export BackendKind, CodegenTarget, OptLevel, OutputFormat
```

This is why `68e3b5b7262` fixed the other sites and not this one: that commit
added an `export use compiler.backend.backend.backend_types.{CodegenTarget}`,
a form the walk DOES follow. The defect is SHAPE-specific, not type-specific —
the same class as `hir_tuple_signature_dependency_unprojected_2026-08-21.md`
and `hir_enum_payload_blockvalue_unresolved_2026-08-21.md`.

## Fix

`_Items/module_reexport_materialization.spl`, non-glob export-route branch: when
the facade does not declare the name and the route is not aliased (the bare
form), resolve to the **package sibling that physically declares it**. Package
siblings already see each other with no import edge
(`resolve_package_sibling_symbols`), so this grants no new visibility — it only
follows a route the surface builder could not record. Reuses the existing
`cached_surface_package_name` + `package_sibling_registry_names` helpers; no
change to module surfaces or resolution order. **Ambiguity stays unresolved:**
two siblings declaring the same short name return not-found rather than guess,
matching the payload path's deliberate exclusion of package inference.

Also added, level-gated and default off, in `hir_lowering/types.spl`:

```
SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1
[hir-unresolved-type-origin] name=... lowering_module=... span_file=... span_line=...
```

so the strict gate names the annotation's real source file instead of only the
module it is blamed on.

## Verification status — HONEST: not behaviourally verified

Both changes lint clean (`bin/simple lint`, 0 errors). Neither has been proven
to change runtime behaviour, for two independent reasons:

1. **The spec harness cannot execute this path on the deployed seed.** A
   fixture mirroring the shape (package `__init__` with `export CodegenTarget`,
   sibling declaring it, importer with `fn aot(t: CodegenTarget)`, consumer
   importing that callable) dies with
   `semantic: method 'lookup_or_invalid' not found on type 'SymbolTable'`
   before reaching the assertion. `SymbolTable` has TWO `impl` blocks
   (`hir_types.spl:236` and `hir_symbol_table_methods.spl:30`); driven from a
   spec, the seed loads only the first, so every method in the second —
   `lookup_or_invalid` among them — is undispatchable. `use
   compiler.hir.hir_symbol_table_methods.*` does not help, and the module has
   no public free function to force-load it. Existing HIR re-export specs pass
   only because their fixtures never reach a call site in that second block.
   **This blocks a reproduce spec for the whole re-export resolution path, not
   just this bug, and should be filed separately.**
2. **A native-build probe is the only remaining path and costs >1h per run.**
   The shared working tree was additionally mid-refactor and non-buildable
   during this investigation (a concurrent session had removed
   `module_surface_name_position` from `module_surface_types.spl` while its
   caller at `_Items/module_import_registration.spl:89` remained), so all
   verification had to move to a clean `git worktree` at HEAD.

Do not treat this as closed until a stage1 lowering of
`compiler.driver.driver_public_api` is observed clean.
