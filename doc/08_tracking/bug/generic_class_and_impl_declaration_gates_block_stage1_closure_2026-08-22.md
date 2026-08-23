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

---

# Iteration 2026-08-23 — pattern/loop-bound type args, and the struct gate

## The blocker that actually stops the stage1 closure at step 3/6

`MonomorphizationPass.env` — the environment `infer_call_type_args` consults —
was seeded ONLY from function parameters (`rewrite_function`) and from `let`
statements (`collect_lets_stmt`). Two binding forms carry neither a `let` nor a
parameter:

- a match arm's pattern variables (`case Int(a): mix(h, a)`);
- a `for` loop's variable (`for t in types: mix(h, t)`).

`collect_lets_expr` descended into both BODIES (`MatchCase(_, arms)`,
`For(_, _, body, _)`) but never bound the names. So `infer_expr_type` returned
nil, `infer_call_type_args` fail-closed to `[]`, and the call raised
`E-MONO-032`, which `driver_hir_pipeline_passes.spl:100` turns into
`E-MONO-033: refusing to lower non-monomorphic HIR to MIR`.

**Scale, by enumeration rather than estimate.** The stage1 closure
(`src/compiler` + `src/runtime` + `src/app/cli`) declares generic functions in
exactly 7 files, all visitor/hasher infrastructure. Call sites that are NOT
themselves inside a generic template (templates are skipped in step 2 and only
their specializations are walked, so their internal recursive calls never
reach the gate) are:

| generic fn | root call sites | argument binding form |
|---|---|---|
| `_hir_mix_prim<T>` (`20.hir/generated/hir_hash.spl`) | 67 | match-arm payload binding |
| `walk_hir_expr<C>` (`35.semantics/enum_contract/hir_match_coverage.spl:233`) | 1 | `val` |
| `profile_region<T>` | 2 | — |
| `owned_global_symbol_names<T>` / `global_symbols_without_names<T>` | 5 | — |
| `mir_visitor_walk_module<V>` | 1 | — |

So **67 of the ~76 real root call sites in the whole stage1 closure were
match-arm bindings**, all in one generated file. This is the dominant
step-3 blocker, and it is not the `Option`/`Result`/`Dict` population the
phase36 forecast predicted — those are builtins that `40.mono` never sees,
since only user-declared generic functions enter `generic_functions`.

### Fix (plan §9.4 "local annotations" / "enum payloads")

`src/compiler/40.mono/monomorphize_integration.spl`:
- new `enum_payload_types: Dict<text, HirType>`, filled in `collect_generics`
  from `module.enums` (enums were not collected at all before), keyed
  `"<Enum>::<Variant>::<index-or-field>"`;
- `collect_pattern_bindings` / `collect_enum_payload_bindings` /
  `bind_payload_pattern` bind a match arm's variables from the pattern's own
  recorded type when concrete, else from the DECLARED variant payload type;
  called from the `MatchCase` arm of `collect_lets_expr` before descending;
- the `For` arm binds the loop variable from the iterable's element type
  (`Array`/`Slice`) when the iterable is locally inferable.

Fail-closed throughout: anything not concretely derivable is left unbound and
still yields the loud `E-MONO-032`. No type is ever guessed, and nothing is
erased to `Any`.

## Generic STRUCT declaration gate opened (was the last declaration-site fatal)

`20.hir/hir_lowering/_Items/declaration_lowering.spl:579` still hard-errored on
any `struct X<T>` (`#158 Phase B`), while the generic CLASS and generic IMPL
gates were replaced by step-12 non-emittable templating on 2026-08-22. The
struct now follows the same rule: `is_generic_template` was already being
recorded truthfully on `HirStruct`, so only the `self.error(...)` was removed.

**Proved by enumeration, not assumed** (the `43ead88be55` precedent):
`grep -rn '^struct <Name><'` over `src/compiler`, `src/runtime` and
`src/app/cli` returns **zero** generic structs, and none of the 28 that exist
under `src/lib` (`ecs`, `ndarray`, `db/accel`, `storage/shared/btree`,
`tooling/ds_utils`, `async`, `common/search`, `src/map`, `src/set`, `tensor`,
`maybe_uninit`, `array_builder`, `engine/resource/handle`) is imported by
anything in the stage1 closure. So the change cannot silently mislower a
stage1 instantiation — there is none. Loudness is preserved at the USE site
(`E-MONO-030/032/033` in 40.mono, `HWIR-E-GENERIC` in strict MIR).

Corollary worth recording: the phase36 forecast's item 3 ("generic structs are
plausibly a large fraction of the residual 50 HIR fatals") is **wrong for the
stage1 closure** — the closure declares no generic struct at all. The gate was
blocking fixtures f01/f12, not stage1.

## What is still NOT fixed

Everything in the previous section's "What is NOT fixed": impl-method
templates are still not collected from `HirImpl`, a `MethodCall` on a generic
receiver still has no instantiation path, and generic STRUCT/CLASS
instantiations (`Box<i64>(v: 7)`) are still not repointed to a specialization —
`rewrite_expr`'s `StructLit` arm rewrites the field expressions only. A
program that really instantiates a generic struct still fails, now at
40.mono/MIR instead of at the declaration.

## Evidence

Reproduce spec (new):
`test/01_unit/compiler/mono/mono_pattern_bound_type_arg_inference_spec.spl`.

End-to-end fixture, closure SIZE = 1 module, built with
`native-build --source <dir> --entry-closure --entry <f>` on the deployed seed
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`:

`f13_mono_match` (enum + `mix<T>` called from two match arms):
- pre-fix: `[mono] generic_fns=1 call_sites=2 specializations=0 unresolved=2`,
  `error[E-MONO-033]`, `monomorphize step 3/6 failed`, rc=1.

### Sub-finding worth its own fix later: an enum match pattern loses its type

`SIMPLE_MONO_DIAG=1` on the reproduce spec shows HIR lowering emits the arm
pattern as

```
HirPatternKind::Enum(HirType(kind: HirTypeKind::Error), Int,
                     Tuple([HirPattern(has_type_: false, type_: nil,
                                       Binding(SymbolId(4), false))]))
```

i.e. the `Enum` pattern's `type_` is `HirTypeKind.Error` and the sub-pattern
carries no type at all — `case Int(a):` never spells its enum, and lowering
does not resolve it from the scrutinee. That is a HIR defect independent of
mono; anything downstream that wants a pattern's type has the same problem.

Mono is made robust WITHOUT relying on it, by two ordered fallbacks, both
fail-closed:
1. derive the enum name from the SCRUTINEE's inferred type (`match_enum_hint`);
2. if that also fails, accept a `"::<Variant>::<slot>"` suffix only when it is
   declared by exactly ONE enum in the whole program — two or more matches
   leave the name unbound so the loud `E-MONO-032` stands rather than a guess.

Fixing the HIR side (resolve the pattern's enum type from the scrutinee at
lowering time) would let fallback 2 be deleted; it is not attempted here
because it touches pattern lowering for every backend.

## Evidence (verified)

Reproduce spec `test/01_unit/compiler/mono/mono_pattern_bound_type_arg_inference_spec.spl`:
- pre-fix (for-loop half only implemented): `2 total, 1 passed, 1 failed` —
  the enum half reported `expected 2 to equal 0`;
- post-fix: `2 total, 2 passed, 0 failed`, with the diag confirming the
  scrutinee hint resolving the key: `bind payload key='Lit::Int::0' known=true`.

Regression sweep, deployed seed
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`:

| spec | result |
|---|---|
| `mono_source_inference_fixed_point_spec` | 5/5 |
| `mono_template_pruning_spec` | 4/4 |
| `generic_class_impl_template_lowering_spec` | 5/5 |
| `monomorphization_native_build_regression_spec` | 2/2 |
| `monomorphize_integration_spec` | 18/18 |
| `free_generic_fn_two_module_native_spec` | 0/4 — **pre-existing RED, not caused here** |

The last row was A/B'd: `git stash` of the two changed source files and a
re-run produced a **byte-identical** failure list on the unmodified base
(`expected 2 to equal 0` / `expected true to equal false` / `expected 1 to
equal 0` x2). It is red at `origin/main` and is filed separately.

Gate: `sh scripts/check/check-perf-regression-tests.shs` ->
`PASS — 81 mechanism(s) checked, 0 regressed` (up from 78; 8 new rows pinning
each binding form, the scrutinee hint, and the struct gate staying open).
