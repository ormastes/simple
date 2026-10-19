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

Commit on `work/eq-ord-hir-workaround-20261019`: drop the `Eq`/`Ord` where
bounds (keep `Hash`), tagged `@workaround bug=eq_ord_where_bound_unresolved_hir_2026_10_19
recover=b73c24d606e`. Semantics-neutral for native output: bounds are erased,
and every producer before `5b649fb61fe` dropped them anyway. Recover the intended
code from `b73c24d606e` once the root fix is in the deployed producer.

## Fix owner / prevention

Root fix: HIR resolves builtin trait bounds without a type-position error
(branch `work/hir-builtin-trait-bound-20261019`), with a spec reproducing
`fn f<K>(k: K) -> bool where K: Ord + Eq`. Remove the workaround in a separate
linked change after the fixed producer passes Phase 3.

DB reconciliation pending (`simple check-dbs` not run on this host).
