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
2. DONE (template-symbol relocation): before an instance from template
   module T is placed in F, `relocate_template_body_v1`
   (`40.mono/monomorphize/hir_subst/body_subst.spl`) rewrites every
   `Var`/`NamedVar` naming a T non-generic function or T constant to
   `NamedVar(<fresh F id>, "<T>.<name>")` -- the exact
   `qualify_imported_function_symbol` spelling MIR takes as the direct callee
   name (externs keep their bare C name) -- and registers those ids in F's
   symbol table (`mono_template_symbol_relocation_v1.spl`). Nested generic
   calls stay on F's worklist. `must_export_for_templates(func,
   reachable_from_generic)` + `mono_template_reachable_helpers_v1(T)` (one
   T-local walk) decide T's export set; the LLVM backend already emits every
   function with external linkage, so no backend change was needed. A
   closure-valued T constant is `E-MONO-041: cannot relocate closure `<n>`
   from <T> into <F>` and the instance is not placed (caller falls back to
   MONO-PENDING). Spec: `test/01_unit/compiler/mono/mono_template_symbol_relocation_spec.spl`
   (UNRUN, same Windows parser blocker). Still open: (a) the `<T>.<name>`
   form matches T's definition only where T's functions are emitted
   module-qualified (bootstrap `--entry-closure`); the plain per-file
   build must qualify T's definitions the same way, or the export helper
   must drive it; (b) relocated T constants/statics rely on MIR resolving a
   `NamedVar` const to T's `g_...` storage -- unverified; (c) T-nested
   types/impl methods referenced from a body are not yet in the plan.
3. Driver wiring: per-file worker supplies `templates` (from the
   `generic_tldr_view_table_v1` / `mono_module_plan_v1` views or `.rr`
   usage refs) and calls the module-scoped entry when the gate is on.
4. Cranelift / non-LLVM backends ignore `is_comdat` (would duplicate-define).
5. Stage2 bootstrap with the gate on, compared against the global path.
