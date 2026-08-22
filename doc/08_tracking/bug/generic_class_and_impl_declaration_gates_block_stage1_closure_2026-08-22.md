# HIR: generic CLASS + generic IMPL declaration gates blocked the stage1 closure (2026-08-22)

**Status: FIXED** (declaration-site half). Supersedes the scope of
`hir_generic_impl_methods_native_path_poll_2026-08-22.md`, which covered only
`async/poll.spl`; the run13 log carries **three** sites in **two** files.

## Exact site list (run13 stage1 HIR phase)

    grep -oE 'error in src/[^:]*: (generic|monomorphization)[^|]*' stage1_build13.log | sort | uniq -c

| n | file | tier | text |
|---|---|---|---|
| 1 | `src/lib/nogc_async_mut/async/future.spl` | class | `generic classes are not supported ... class 'Future' declares type parameter(s)` |
| 1 | `src/lib/nogc_async_mut/async/future.spl` | impl  | `generic struct/class methods are not supported ...` |
| 1 | `src/lib/nogc_async_mut/async/poll.spl`   | impl  | `generic struct/class methods are not supported ...` |

No `generic structs are not supported` site fires in this closure, so the
struct-tier gate (`_Items/declaration_lowering.spl:579`) is deliberately LEFT
IN PLACE.

## Root cause: the gate was at the wrong place in the pipeline

All three fatals fire at the DECLARATION site, unconditionally, regardless of
whether anything instantiates the template. Measured over the 747 source paths
in the run13 log: **every** occurrence of `Future<`, `Future(`, `Future.`,
`Poll<`, `Poll.Ready`, `Poll.Pending` outside `src/lib/nogc_async_mut/async/`
is inside a comment, docstring, or diagnostic string literal
(`frontend/desugar/{desugar_async,poll_generator,state_enum}.spl`,
`hir/hir_lowering/async_errors.spl`). **Zero real instantiations reach the
stage1 closure.** The closure was blocked by declarations nothing uses.

## Fix (hardening plan §9.3 step 12: "mark generic templates non-emittable")

1. `50.mir/_MirLowering/module_lowering.spl` — both function-emission loops
   (the function-symbol loop and `lower_module`'s `fn_values` loop) now SKIP
   `is_generic_template` functions. This closes the gap `prune_consumed_
   templates` documents in its own docstring: a template with ZERO
   instantiations was kept, and MIR lowered it anyway.
2. `20.hir/.../_Items/class_declaration_lowering.spl` — the class-tier fatal is
   replaced by templating; the class's inline methods now get
   `is_generic_template = true`, matching what the impl tier already did.
3. `20.hir/.../_Items/trait_impl_lowering.spl` — the impl-tier fatal is
   removed; its per-method `is_generic_template` marking was already present
   and is now the whole mechanism.

Declaring a template is not the defect; EMITTING one is.

## Loudness is preserved, moved downstream

A REACHABLE instantiation still fails hard, at two independent layers:
- `40.mono` emits `E-MONO-030`/`E-MONO-032` for every generic call site it
  could not rewrite, and `80.driver/driver_hir_pipeline_passes.spl` turns each
  into a `ctx.add_error` (they are errors, not warnings);
- `50.mir/hwir/mir_to_hwir.spl:590` rejects a non-elaborated generic function
  with `HWIR-E-GENERIC` on the strict path.

## What is NOT fixed (still #158 Phase C)

Real instantiation-driven monomorphization of generic structs/classes and of
impl methods. `40.mono` (625c245bafa) specializes FREE generic fns only: impl
methods are not in `module.functions`, so the pass never sees them, and a
`MethodCall` on a generic receiver has no instantiation path. A user that
actually writes `Poll<i64>` and calls `.is_ready()` still fails — now at
40.mono/MIR instead of at the declaration. Needed: collect impl-method
templates from `HirImpl`, derive type args from the RECEIVER type, specialize,
repoint by mangled name, extend `prune_consumed_templates`.

## Evidence

Spec `test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl`
(reduced `impl Poll2<T>` + `class Fut<T>`, both uninstantiated):
pre-fix `3 passed, 2 failed` (rc=1), post-fix `5 passed, 0 failed` (rc=0),
proved by `git stash` of the three source files and re-running.
No regression: `mono_template_pruning_spec` 4/4,
`free_generic_fn_two_module_native_spec` 4/4,
`monomorphization_native_build_regression_spec` 2/2.
Verified with the deployed seed `/mnt/data/worktrees/goal-main-1/bin/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`.
