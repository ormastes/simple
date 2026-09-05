# `use pkg.Mod.{Mod}` binds the module namespace dict, not the class

**Date:** 2026-08-17
**Status:** FIXED (Rust seed source; awaiting next seed/bootstrap redeploy)

## Symptom

When a module FILE shares its name with an exported class (`pkg/Mod.spl`
containing `class Mod`), an explicit group import `use pkg.Mod.{Mod}` bound
`Mod` to the module namespace dict `{Mod: <constructor:Mod>}` instead of the
class. Consequences:

- `Mod.static_fn()` silently returned `nil` (dict `.get`-style lookup)
- `x is Mod` was always `false`
- Constructor calls `Mod(...)` happened to still work (constructor lookup path)

Reported as the cause of MDSOC entity-view failures (per-entity module files
named after their class, e.g.
`src/compiler/85.mdsoc/transform/feature/mir_to_backend/entity_view/MirProgram.spl`
imported as `...entity_view.MirProgram.{MirProgram}` from `MirView.spl`).

## Root cause

Two sites in the Rust seed interpreter unpack a group import's members into
the env, then unconditionally rebind the module dict under the module's
basename — clobbering an explicitly imported member of the same name:

- `src/compiler_rust/compiler/src/interpreter_eval.rs` (`Node::UseStmt`,
  "keep the module dict under its name for qualified access")
- `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
  (`process_use_stmt`, non-glob arm — Glob already had a guard)

The pure-Simple interpreter (`src/compiler/10.frontend/core/interpreter/`)
uses flat symbol tables and does not exhibit the bug.

## Fix

At both sites: when a `Group` import explicitly names an item (or alias)
equal to the module's own binding name, skip the module-dict rebind so the
member wins. Aliased items (`{Mod as Other}`) leave the dict bound under
`Mod` unchanged.

## Tests

- Reproducer (fails before fix — `Widget.kind()` nil — passes after):
  `test/01_unit/compiler/module_resolver/group_import_self_named_module_spec.spl`
- Generalization (nested self-named module, sibling fn in same group, alias
  form): `test/01_unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl`
- Fixtures: `test/01_unit/compiler/module_resolver/fixtures/self_named/`
- All mirrored identically under `test/unit/compiler/module_resolver/`.

Verified 2026-08-17 with a seed rebuilt in an isolated CARGO_TARGET_DIR:
both specs pass; `test/01_unit/compiler/mdsoc` unchanged at 317/324
(remaining 7 failures are a distinct `.?`-semantics issue in
`layer_checker_spec.spl` (6) plus one unresolved-module in
`pipeline_integration_spec.spl` — out of scope here).

## Not fixed here (adjacent, pre-existing)

- `x is StructType` returns `false` for struct instances under `run`
  (reproduces with non-shadowed imports; unrelated to import binding).
