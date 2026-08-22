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

---

## Round 2 (2026-08-21) — the FIRST fix works; a SECOND export shape does not

Stage1 run7 (tree `d1fd6255ecd`), which contains `4368a77f7fa`, still reported
`unresolved type: CodegenTarget` against `driver_public_api.spl`. That is not a
regression of the first fix — it is a *different* export shape on the same
route.

### The spec-harness blocker above was wrong

The "`lookup_or_invalid` is undispatchable from a spec" claim is not what blocks
the fixture. A fixture built on the same harness as
`test/01_unit/compiler/hir/same_named_package_facade_reexport_spec.spl`
(`module_surfaces_from_modules` + `hirlowering_for_module(...).lower_module`)
executes the whole re-export resolution path fine. The real defect in the
earlier attempt was that the **consumer module was omitted from the surface
registry**: lowering then emits `missing importing module surface for
<consumer>` and every subsequent name fails to resolve, which is what made the
fixture look blocked. Adding the consumer to both `modules` and `sources` makes
the fixture green/red on the actual defect. **No separate bug should be filed
for `lookup_or_invalid`.**

With a correct fixture, measured on the deployed seed:

| shape | pre-`4368a77f7fa` | at HEAD (round 2) |
|---|---|---|
| bare `export CodegenTarget`, sibling DECLARES it | fail | **pass** |
| bare `export CodegenTarget`, sibling only `export use`s it | fail | **pass** |
| qualified `export backend_types.CodegenTarget` | fail | **fail** |

So `4368a77f7fa` is real and load-bearing, and it covers both bare shapes. What
it does not cover is the **qualified bare export**.

### Root cause of the remaining shape

`src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl:391-400`
(non-glob export branch) stores the export item verbatim. For
`export backend_types.CodegenTarget` that records

    export_route_sources[i] = "backend_types.CodegenTarget"
    export_route_locals[i]  = "backend_types.CodegenTarget"
    export_route_target_indices[i] = -1

so in `find_reexport_source_walk`
(`_Items/module_reexport_materialization.spl`) the guard `exp_local == wanted`
compares the whole dotted string against the short name a consumer writes
(`CodegenTarget`) and **the route is skipped outright** — it never reaches the
declares-check, the alias recursion, or the round-1 package-sibling branch. The
qualifier, which names the sibling that owns the name, is discarded.

`src/compiler/70.backend/backend/__init__.spl:326` spells the CodegenTarget
re-export exactly that way (`export backend_api.CodegenTarget`). The shape is
not rare: `grep -rn '^export [a-z_][a-z_0-9.]*\.[A-Za-z]' src --include=*.spl`
counts **509** qualified bare exports, including all of
`src/compiler/00.common/diagnostics/__init__.spl` (`export span.Span`, …) and
~90 lines of `70.backend/backend/__init__.spl`.

### Fix

Two lines of route structure, no new visibility and no import added to any
driver module:

1. `module_surface_registry_index.spl`, non-glob branch: when an export item
   carries no `:` alias but does carry a `.`, split the last segment off as the
   member name and resolve the qualifier to a module key — first against the
   facade's own **registry** package (`preferred_registry_name` minus its last
   segment; `surface.package_name` and `canonical_name` are filesystem-derived
   and disagree with registry keys), then the relative rule, then absolute.
   On success record `source = local = member` and the resolved module as the
   route target, exactly as the `.*` glob branch already does. If the qualifier
   resolves to nothing the route is stored verbatim as before — fail-safe.
2. `_Items/module_reexport_materialization.spl`, non-glob branch: follow that
   recorded target first (declares-check, then recurse), before the existing
   facade-declares / alias / package-sibling attempts.

### Verification

- Reproduce spec: `test/01_unit/compiler/hir/package_export_route_shapes_spec.spl`,
  three shapes. Pre-fix 2 pass / 1 fail (the qualified shape, with the exact
  `unresolved type: CodegenTarget`); post-fix 3/3.
- Neighbouring re-export specs
  (`same_named_package_facade_reexport_spec`, `module_surface_glob_export_origin_spec`,
  `reexport_physical_cache_spec`) have **byte-identical** pass/fail counts
  before and after the change (2/3, 3/1, 1/15 — all pre-existing failures,
  none introduced here).

## Round 3 (2026-08-22) — env-gated exemption: the rescue only ran with SIMPLE_BOOTSTRAP=1

**Status: RESOLVED in tree (core fix).**

### Root cause

Stage 1 run9 (`fp9/run9.sh`) runs the seed `native-build --entry-closure
--threads 8` with **no** `SIMPLE_BOOTSTRAP` in the environment. Every one of
the 17+ `unresolved name/type: X` shapes it died on (`CodegenTarget`,
`BlockValue`, `MirType`, `parser_type_kind_named_name`, `TypeLayout`,
`MirStatic`, `GpuIntrinsicKind`, `HirIfArm`, `HirFunction`, `CompiledModule`,
`CompilationContext`, `mir_transfer_mode_consumes_source`, ...) is the
documented GLB2 second-level-glob / package-sibling residual: `use m.*`
expands only what `m` declares or `export`s, never what `m` itself reaches
through its own plain `use n.*`. The ONLY rescue for that residual was
`try_register_bootstrap_global_symbol` (unique-owner fallback), gated on
`SIMPLE_BOOTSTRAP=1`. Same defect class as d2bdc42d8ad (eprint/generic):
an environment variable was silently load-bearing for correctness.

### Fix (no env gates)

1. `_Items/module_import_registration.spl`: new
   `try_register_glob_reachable_symbol(name, span)`, called first from
   `try_register_bootstrap_global_symbol` **before** the env check. It is
   name-directed: for ONE unbound name it visits only the importer's glob
   targets, and for each target either takes the target's own declaration or
   delegates the second-level hop to `find_reexport_source` (registry-pure,
   memoized, depth-capped). Nothing is expanded that the name does not need,
   so the >13 min / 8.5 GB cost that blocked ungating GLB2 is not incurred.
2. `_Items/module_reexport_materialization.spl`, bare-export package-sibling
   inference: a sibling that RE-EXPORTS the name (`export use other.{Name}`)
   now counts as an owner (walked to its terminal) under the same uniqueness
   rule as a sibling that declares it. Ambiguity (two distinct terminals)
   still returns not-found rather than guessing.
3. `SIMPLE_REXMEMO_VERIFY=1` diagnostic: re-walks on every REXMEMO memo hit
   and prints `[rexmemo-mismatch]` if the memoized terminal disagrees. Probe
   runs of driver.spl and interpreter.spl with the verifier on produced
   **zero** `[rexmemo-mismatch]` lines, so the f8681a7afa6 miss-caching is
   not implicated.

### Verification

- `test/01_unit/compiler/hir/package_export_route_shapes_spec.spl` (16
  examples; 13 new multi-hop / second-level-glob / sibling shapes):
  pre-fix 11 pass without `SIMPLE_BOOTSTRAP`; post-fix **16/16 without**
  `SIMPLE_BOOTSTRAP` and 16/16 with it.
- Single-module `native-build` of `src/compiler/driver/driver.spl` and
  `src/compiler/backend/backend/interpreter.spl` (`--threads 2`, no
  `SIMPLE_BOOTSTRAP`): see the landing commit message for the
  `unresolved name/type` counts.
