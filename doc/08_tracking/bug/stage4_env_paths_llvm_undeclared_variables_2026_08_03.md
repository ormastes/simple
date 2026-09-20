# Stage4 env paths emitted an undeclared `variables` LLVM global

- **Date:** 2026-08-03
- **Status:** FIX IMPLEMENTED — STAGE4 VERIFICATION PENDING
- **Severity:** P1
- **Area:** pure-Simple HIR import ownership
- **Owner:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
- **Exact source:** `src/lib/nogc_async_mut/env/paths.spl`

## Recorded failure

The real Stage4 entry closure reached `env/paths.spl` and failed LLVM
validation with:

```text
llvm codegen: semantic: llvm global load referenced undeclared symbol variables
```

The source selectively imports `env_get` through
`use std.env.variables.{env_get}`. A qualified module tail must not escape HIR
as a value receiver when the selected callable has already been bound to its
retained physical `ModuleSurface` owner.

## Owner repair

Module import lowering now resolves aliases through the aligned retained
surface index and registers imported callables against that physical owner.
Module-only namespace symbols use the same owner. This avoids lowering an
alias-only namespace receiver as `LoadGlobal` while keeping real unresolved
globals fail-closed at the LLVM boundary.

## Regression evidence (2026-08-17)

`test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl` now
covers the previously missing selective-import topology directly:

- exact `use std.env.variables.{env_get}`;
- adjacent `use std.env.variables.{env_get as read_env}`;
- no MIR `LoadGlobal` named `variables` or ending in `.variables`;
- a direct call whose terminal owner is `env_get`.

The deployed pure-Simple macOS test runner passed all five cases. A focused
pure-Simple native shard compile of the real `env/paths.spl` also passed the
historical undeclared-global point, then stopped later with the separate
diagnostic `runtime error: field access on nil receiver`; it did not produce a
fresh Stage4 artifact. Therefore this row remains verification-pending rather
than fixed.

## Closure gate

Run one provenance-admitted current Stage4 entry closure. Close the row only
when the real env paths shard emits no undeclared `variables` global, LLVM
verification passes, and the Stage4 binary is produced. Track the later nil
receiver independently if it reproduces on the admitted current compiler.

## Fix evidence — 2026-09-17 (stage4_env_paths_llvm lane)

The row stayed open because the guarding spec could not pass at origin/main
and the HIR import boundary had regressed for exactly the topology this row
tracks. Three distinct defects were found and repaired, all in pure Simple:

1. **`resolve_import_symbols` hard-failed single-module consumers.**
   The September refactor of `src/compiler/20.hir/hir_lowering/_Items/
   module_import_resolution.spl` made the importing module's OWN surface
   mandatory: when `importer_surface_index < 0` it emitted
   `missing importing module surface` and returned before registering any
   import. The 2026-08-17 version of this function read import items straight
   from the parser's import decls and had no such requirement, which is why
   the record's "five cases pass" evidence existed. The importer's surface
   rows are a verbatim flatten of the parser's own imports
   (`module_surface_declarations.spl`), so the repair reads the identical
   rows from the live parser import decls when (and only when) the importer
   surface is absent. The real entry closure is untouched — every closure
   module has a registered surface there. This was the reason all five
   spec scenarios failed at origin/main, including the three namespace
   scenarios the 2026-08-03 repair had already fixed once.

2. **Aliased callable imports kept the alias as the emitted callee name.**
   `register_imported_symbol_inner`'s callable branch defined the symbol
   under the local alias (`use m.{f as g}` -> stored name `g`) and, unlike
   the composite / enum / trait / type-alias branches right above it, never
   restored the physical declaration name. The call site then baked the
   alias into the MIR callee operand, referencing a definition no module
   emits — the exact undeclared-symbol-at-LLVM defect family this row
   tracks, reproduced in the spec's adjacent `env_get as read_env` case.
   The repair applies the sibling branches' established policy: rename the
   fresh symbol to `imported_name` when the local name was not already
   bound and differs from the physical name
   (`module_import_registration.spl`, callable branch). `read_env("PATH")`
   now lowers to a direct `env_get` call owned by the retained variables
   surface.

3. **The spec itself had been gutted by an Aug-28 merge.** Commits
   `e274cd33719a` / `a8244005f9be` ("merge all share-history worktree
   branches") dropped `verify_selective_env_import_lowering` from
   `test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl`
   while keeping its two `it` blocks, so scenarios 4–5 failed with
   `semantic: function verify_selective_env_import_lowering not found`.
   The function was restored from `96a260a5a62d` unchanged.

Guard evidence (SIMPLE_LIB=src, seed interpreter, this workspace):

- Before: `Results: 5 total, 0 passed, 5 failed`
  (three namespace scenarios: `missing importing module surface` ->
  unresolved `variables`/`path`/`platform` receivers; two selective
  scenarios: `function verify_selective_env_import_lowering not found`).
- After: `Results: 5 total, 5 passed, 0 failed` — all five cases green,
  including `no MIR LoadGlobal named variables` and direct `env_get` calls
  in both the exact and the aliased selective-import topologies, forward
  and reverse overlay discovery.

The real `src/lib/nogc_async_mut/env/paths.spl` import line was not
modified and LLVM validation was not weakened, per the lane constraints.

## Real-shard A/B evidence — 2026-09-17

`bin/simple native-build src/lib/nogc_async_mut/env/paths.spl` (single
positional shard, the record's reproducer) was attempted in this jj
workspace. The SCV provenance admission requires a git event source, which
a jj workspace does not carry; a throwaway git mirror of the workspace tree
under `/tmp/scv-fakegit` (GIT_DIR/GIT_WORK_TREE only — no project VCS
state touched, both cold-init flags set) satisfied admission.

Result: the shard reaches `phase=hir` and fails identically WITH and
WITHOUT this lane's fix (pristine origin/main content A/B):

```text
[hir-reexport-chase-unresolved] facade=lib.nogc_sync_mut.path item=Option ...
[hir-callable-dep-origin-unresolved] owner=lib.nogc_sync_mut.path dependency=Option ...
error: semantic: cannot call mutating method 'push' on immutable array 'existing'
```

while lowering `lib.nogc_async_mut.path` (the `export use
std.nogc_sync_mut.path.*` compatibility facade). None of the nine shard
modules contains a variable named `existing`, so the last diagnostic is
the seed JIT-compiling a pure-Simple compiler function that carries a
`val existing` + `.push` pattern, reached through the facade's re-export
chase for the builtin `Option`. That defect is PRE-EXISTING at
origin/main (A/B verified) and blocks the shard before the historical
undeclared-`variables` point; it is not introduced by this lane's fix,
which is behavior-neutral on this shard (its importer surfaces all exist,
so the parser-item fallback never fires, and no aliased callable import
is present). File it as the next env-paths shard blocker.
