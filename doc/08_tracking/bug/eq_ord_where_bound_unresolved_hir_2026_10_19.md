# eq_ord_where_bound_unresolved_hir_2026_10_19

- Status: open (workaround active)
- Severity: blocks Phase 3 bootstrap (HIR fatal, 2 modules poisoned)
- Found: 2026-10-19, Phase 3 with producer4
  (`C:/dev/simple-bootstrap-storage/producer4-20261019/strict/simple-producer4-strict.exe`,
  built from origin/release_phase3 `02ca1461937`), log
  `C:/dev/simple-bootstrap-storage/p3p4-20261019/compile.log`.

## Failure

```
HIR lowering error in .../src/lib/nogc_sync_mut/sffi/ordered_key_cmp.spl: unresolved type: Ord
HIR lowering error in .../src/lib/nogc_sync_mut/sffi/ordered_key_cmp.spl: unresolved type: Eq
HIR lowering error in .../src/app/optimize/sprof_collection_profile.spl: unresolved type: Eq / Ord (x4 each)
```

Affected source: `src/lib/nogc_sync_mut/sffi/ordered_key_cmp.spl:9,16`
(`where K: Ord + Eq`) and `src/app/optimize/sprof_collection_profile.spl:257,261,284,287`
(`where K: Hash + Eq + Ord`). `Hash` resolves (imported via `use std.hash.Hash`);
`Eq`/`Ord` have no declaration anywhere in `src/**` -- they exist only as builtin
traits in `src/compiler/25.traits/trait_validation.spl:135,140`.

## Root cause

`5b649fb61fe` (PR #3763, "fix(frontend): preserve ordinary generic function
bounds") started transporting `where` bounds through the flat-AST bridge
(`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
`convert_decl_function_type_params`). Before it, `ParserTypeParam.bounds` was
always `[]`. HIR `lower_type_param`
(`src/compiler/20.hir/hir_lowering/types.spl:1415-1416`) lowers every bound with
the ordinary `lower_type`, whose strict gate (`types.spl:1402`) hard-errors on any
name with no symbol -- so builtin trait bounds (`Eq`, `Ord`, ...) that have no
source declaration became fatal. Not #3807 (`9697890ad02` is already in the
passing producer2 base `d54d221ee124`).

## Workaround

Workaround commit `d28b2b8eeb9` (PR #3886, merged as `9c9a48ac254`): drop the
`Eq`/`Ord` where bounds (keep `Hash`), tagged `@workaround bug=eq_ord_where_bound_unresolved_hir_2026_10_19
recover=b73c24d606e`. Semantics-neutral for native output: bounds are erased,
and every producer before `5b649fb61fe` dropped them anyway. Recover the intended
code from `b73c24d606e` once the root fix is in the deployed producer.

## Fix owner / prevention

Root fix: PR #3887 (branch `work/hir-builtin-trait-bound-20261019`).
`HirLowering.bound_is_undeclared_builtin_trait`
(`src/compiler/20.hir/hir_lowering/types.spl`) erases a bare builtin solver
trait bound (Clone, Copy, Debug, Default, Drop, Eq, Ord) when no symbol of that
name is in scope; declared/imported traits and unknown names are unchanged.
Builtin bounds are erased rather than resolved to `builtin_trait_symbol(id, name)`
because the solver has no builtin impls for primitives, so resolving them would
reject every call. Unchecked obligations are filed as
`doc/08_tracking/bug/builtin_trait_where_bounds_erased_unchecked_2026_10_19.md`.

Prevention spec: `test/01_unit/compiler/20.hir/builtin_trait_where_bound_spec.spl`
(`where K: Ord + Eq`; `Hash + Eq + Ord` with declared Hash; user-declared
`trait Ord` shadowing; `Ord + MissingTrait` erroring on MissingTrait only).
Not yet executed: this Windows host has no full-CLI pure-Simple binary (the
seed fails to parse `windows_redirected_process.spl`).
Remove the workaround in a separate linked change after the fixed producer
passes Phase 3.

DB reconciliation pending (`simple check-dbs` not run on this host).
