# HIR qualified-symbol lookup was a linear scan; `callable_deps` dominated HIR lowering

**Date:** 2026-08-22
**Status:** FIXED
**Area:** compiler / 20.hir / import lowering
**Severity:** performance (superlinear, whole-build)

## Symptom

`SIMPLE_HIR_PHASE_PROFILE=1` on a full stage-1 build (run12,
`native-build --source src/app --entry-closure --entry src/app/cli/bootstrap_main.spl`)
reported `callable_deps` as the largest exclusive term in the HIR phase, by a wide
margin. Aggregated over the 397 `[hir-prof-excl]` module lines:

| term | exclusive total |
|---|---|
| callable_deps | 5,241,657 ms |
| field_dep | 3,415,298 ms |
| sigtype | 1,652,673 ms |
| declared_dep | 1,316,324 ms |
| project | 1,085,920 ms |
| imports | 776,237 ms |
| explicit_dep | 373,868 ms |
| glob | 282,472 ms |
| methods | 234,412 ms |
| scan | 104,454 ms |
| fields | 100,921 ms |
| functions | 93,423 ms |
| payload | 87,457 ms |
| define | 87,304 ms |
| enums | 72,214 ms |

For `src/compiler/mir_opt/mir_opt/cse.spl` the exclusive line read
`imports=951ms glob=144ms enums=560ms functions=7ms callable_deps=14693ms` —
callable-dependency computation was 10-100x every other term for that module.

## Root cause

`SymbolTable.lookup_qualified_type_raw` (`src/compiler/20.hir/hir_types.spl`)
was a **linear scan over three parallel arrays** with **two text comparisons per
row**:

```
while index < self.qualified_type_module_names.len() and ...:
    if self.qualified_type_module_names[index] == module_name and
       self.qualified_type_member_names[index] == member_name:
        return self.qualified_type_ids[index]
```

`materialize_imported_callable_dependency`
(`20.hir/hir_lowering/_Items/module_reexport_materialization.spl`) issues up to
**three** of these probes per named type, per parameter/return of every imported
callable, per importing module — a miss costs the FULL table length, and the
run12 profile counters show **1,496,719 probes with 1,251,806 misses (84%)**
across the build; for `cse.spl` alone, 4,375 probes / 2,857 misses, i.e.
~3.4ms **per probe**. Total cost was therefore
O(modules x callables x deps x qualified-bindings).

`bind_qualified_type` / `bind_qualified_function` were the same shape: an O(n)
dedup scan per bind, plus `self.x = self.x.push(v)` on three fields — the
copy-on-write alias antipattern from `.claude/rules/code-style.md`, so building
the table was itself O(n^2).

The fix is not a new index. A `qualified_types: Dict<text, i64>` was **already
maintained in lockstep by `bind_qualified_type`, its only writer** — and is the
only form the HIR codec serializes (`20.hir/generated/hir_codec.spl:5676`
reconstructs `SymbolTable` from the Dicts and drops the arrays entirely). The
Dict was already the more authoritative store; the hot lookup simply never read
it.

## Fix

`src/compiler/20.hir/hir_types.spl` (QTYPEIDX):

- deleted the five write-only parallel arrays (`qualified_function_names`,
  `qualified_function_ids`, `qualified_type_module_names`,
  `qualified_type_member_names`, `qualified_type_ids`);
- `bind_*` / `lookup_*_raw` are now `contains_key` + index reads on the existing
  `qualified_functions` / `qualified_types` Dicts — O(1), and the CoW pushes are
  gone;
- key is `qualified_symbol_key(module, member) = module + "#" + member`. The
  previous `.` join was **not injective**: `("a.b", "c")` and `("a", "b.c")`
  both produced `"a.b.c"`. `#` cannot occur in a module path or a member name.
  The `#` shape matches `module_callables` (MODCALLIDX, 2026-08-21).

Return type stays a raw `i64` — the native-safety reason for the scalar boundary
(a value-type `SymbolId` inside `Optional` can be corrupted by staged native
code) is about the RETURN, not the container, and is preserved.

The bootstrap contract spec
`test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl`
previously froze the array form and forbade `self.qualified_types.has(key)`.
That row is updated deliberately, not routed around: the ban was on the `.has`
guard shape, and the whole subsystem's 2026-08-21 index fixes (PKGDEP, PKGIDX,
IMPLIDX, MODCALLIDX) already use `contains_key` Dict indexes on this exact path.
The spec now pins the Dict index and the injective `#` key instead.

Note on that file's state: it is pre-existing RED on `origin/main` — measured
2026-08-22 at `2d4050cc5e5`, 9 of its 10 rows fail for reasons untouched by this
change (frozen import routes, composite projections, daemon closure binding, the
glob memo). This change moved it from 0/10 to 1/10: the qualified-symbol row is
now the only passing one. The remaining 9 are not this lane's and are left as
found rather than papered over.

### Cache note

`qualified_types` is serialized by the HIR codec, so a blob written with the old
`.` keys would decode into a table whose keys the new lookup cannot find. This
is safe without a format bump because both `object_cache_key`
(`native_project/mod.rs`, folds `compiler_fingerprint()` over `current_exe`'s
bytes) and the pure-Simple `native_build_cache_scope_key` fold the producing
compiler's identity, so changing the compiler already invalidates every entry.

## Reproduce / regression pin

`test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl` — mechanism
pin, not a wall-clock budget: the same number of MISS probes is timed against a
100-binding table and a 4000-binding table, and the ratio must stay under 3x.
Under the linear scan the ratio tracks the size ratio (~40x); under the Dict it
is ~1x. The spec also pins hit/miss correctness at scale, the injective key, the
function-side index, and first-binding-wins on a duplicate bind.

Perf gate row: `scripts/check/check-perf-regression-tests.shs`.

## Measured result

`src/compiler/mir_opt/mir_opt/cse.spl`, `[hir-prof-excl]` (ms):

| term | before (run12) | after |
|---|---|---|
| **callable_deps** | **14,693** | **401** (~37x) |
| declared_dep | — | 1,123 |
| field_dep | — | 828 |
| imports | 951 | 301 |
| glob | 144 | 61 |
| enums | 560 | 594 |
| functions | 7 | 9 |

`callable_deps` is no longer the dominant term for that module — it now sits
behind `declared_dep` and `field_dep`. The terms this fix does not touch
(`enums`, `functions`) are unchanged, which is the control: the drop is
attributable to the lookup, not to a quieter box.

**Caveat, stated rather than papered over:** the "before" column is run12's
number, taken on a different entry closure (`src/app` vs `src/compiler`) and a
differently-loaded machine, so 37x is an envelope, not a controlled A/B. The
controlled evidence is the mechanism spec — identical miss-probe count against a
100-binding and a 4000-binding table, ratio required under 3x — which fails
pre-fix and passes post-fix, isolating table size as the only variable.

## Related

Same defect family (a per-operation full copy/scan invisible at fixture scale):
- `doc/08_tracking/bug/seed_receiver_multi_hop_cow_clone_2026-08-22.md`
- `doc/08_tracking/bug/hir_codec_writer_quadratic_cow_clone_2026-08-22.md`
- `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`
