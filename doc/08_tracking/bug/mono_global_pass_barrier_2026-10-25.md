# Mono global pass is a phase barrier (2026-10-25)

**Status:** opt-in module-scoped path landed (`SIMPLE_MONO_MODULE_SCOPED=1`
gate + `run_monomorphization_module_scoped_v1`); default still global.
Design: `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md`
§4 P4, `build_runner_fiber_scheduler_v1.md` §8.

## Measured

`MonomorphizationPass.process_modules` on the 1442-module bootstrap closure:
roots=23014, roots_rewritten=7279, collect_ms=43883, roots_ms=219560
(~263 s total), all before any object can be emitted.

## Mechanism

`process_modules` collects generics from EVERY module, rewrites every root,
drains one global worklist, then places each specialization into its
TEMPLATE's module. So (a) all HIR must exist before mono starts, and (b)
object F depends on global mono output (its callees live in T's object),
which blocks a per-file worker from emitting F alone.

## Module-scoped contract

`run_monomorphization_module_scoped_v1(module, templates) -> (HirModule,
MonoStats, [text])` (`src/compiler/40.mono/monomorphize_integration.spl`):

- `templates: Dict<text, HirModule>` = template-bearing modules visible to F
  (own + reachable via imports). They are collected read-only, never
  rewritten, never returned.
- Only F's roots and constant initializers are rewritten; the worklist is
  drained only for instances F requested (transitively).
- Every instance is placed into F's own function table with
  `func_attr.is_comdat_instance = true` and an F-owned symbol row.
- Names come from the same `mangled_name`/`mangle_type_args` as the global
  pass, so identical instances from different modules spell one symbol.
- Fail closed: a call in F with generic evidence (explicit type args, an
  imported non-concrete signature, or no declaration) that names no visible
  template records `E-MONO-040: template <name> not visible to module <F>`.

## What the backend emits

`FunctionAttr.is_comdat_instance` -> `MirFunction.is_comdat`
(`apply_function_attr_to_mir`, copied by `with_blocks`) -> MirToLlvm
`fn_comdat`. A flagged function is emitted as

```
$id$i64 = comdat any
define linkonce_odr i64 @id$i64(...) ... comdat { ... }
```

and keeps its bare mangled name (excluded from non-entry module
qualification) so every object spells the same comdat key; the linker keeps
one copy (ELF group / COFF SELECT_ANY).

## Evidence

Spec: `test/01_unit/compiler/mono/mono_module_scoped_spec.spl` (placement +
COMDAT flag, name equality with the global pass, T unchanged, E-MONO-040).
UNRUN: on this Windows host `bin/simple test` fails before the spec with
`parse: in src\lib\nogc_sync_mut\io\windows_redirected_process.spl:
Unexpected token: expected Fn, found Colon` (known host blocker).

## Remaining before flipping the default

1. Run the spec on a host without the parser blocker.
2. Instance bodies still reference template-module-local SymbolIds (calls to
   T's non-generic helpers, T globals). Placing them in F needs those
   references relocated/qualified the way `relocate_mono_types` does for
   types; leaf templates are fine today.
3. Driver wiring: per-file worker supplies `templates` (from the
   `generic_tldr_view_table_v1` / `mono_module_plan_v1` views or `.rr`
   usage refs) and calls the module-scoped entry when the gate is on.
4. Cranelift / non-LLVM backends ignore `is_comdat` (would duplicate-define).
5. Stage2 bootstrap with the gate on, compared against the global path.
