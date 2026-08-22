# HIR glob-reachable resolution re-swept every unbound-name occurrence

**Date:** 2026-08-22
**Status:** FIXED
**Area:** compiler / 20.hir / import lowering
**Severity:** performance (repeated work, whole-build)

## Context: what QTYPEIDX left behind

This is the follow-up lane to
`doc/08_tracking/bug/hir_qualified_type_lookup_linear_scan_2026-08-22.md`
(QTYPEIDX, `5c38b388a53`). That fix made `SymbolTable.lookup_qualified_type_raw`
an O(1) Dict probe and collapsed `callable_deps`, which had been the largest
exclusive term in the whole HIR phase profile. The open question this lane was
opened to answer: **how much of the next four terms — `field_dep` 3,415,298 ms,
`sigtype` 1,652,673 ms, `declared_dep` 1,316,324 ms, `project` 1,085,920 ms in
run12 — did that fix already remove, and what remains?**

### Measured answer

Controlled A/B, same invocation on both sides — `bin/simple run
src/app/cli/bootstrap_main.spl compile --format=smf
src/compiler/mir_opt/mir_opt/cse.spl` with `SIMPLE_HIR_PHASE_PROFILE=1` and
`SIMPLE_TIMEOUT_SECONDS=0`, one worktree at `5c38b388a53` (post) and one at
`5c38b388a53~1` (pre), run concurrently on the same box so machine load is
shared rather than confounded. `[hir-prof-excl]` totals aggregated over the
per-module lines.

`[hir-prof-excl]` exclusive ms, summed over the **16 modules both runs had
completed**, so every row compares the same work on both sides:

| term | pre (`5c38b388a53~1`) | post (`5c38b388a53`) | raw | **attributable** |
|---|---|---|---|---|
| field_dep | 36,901 | 4,055 | 9.1x | **~7.6x** |
| sigtype | 13,192 | 1,188 | 11.1x | **~9.3x** |
| project | 12,819 | 820 | 15.6x | **~13x** |
| declared_dep | 6,186 | 3,229 | 1.9x | **~1.6x** |
| callable_deps | 28,978 | 2,143 | 13.5x | **~11.3x** |
| *enums (control)* | 4,421 | 3,433 | *1.3x* | — |
| *functions (control)* | 2,143 | 1,989 | *1.1x* | — |

`enums` and `functions` are the **controls**: neither reaches
`lookup_qualified_type_raw`, and both move only 1.1-1.3x, which is the residual
box-load difference between the two concurrent runs rather than any effect of
the fix. Dividing through by that ~1.2x control floor gives the attributable
column.

So the answer to the question this lane was opened on: **QTYPEIDX already
removed the large majority of `field_dep`, `sigtype` and `project`** — all three
reach the lookup, `field_dep` by three direct probes per named type and the
other two through `imported_surface_type_projected`. **`declared_dep` is the
term it barely touched**: at ~1.6x it is close to the control floor, because its
body is a `register_imported_symbol` call whose costly children are all
separately profiled slots, so little of the lookup's cost was ever charged to
it. At 3,229 ms against the controls' 3,433/1,989 ms it is no longer a
superlinear outlier, and no second superlinear defect remains in it.

The other consequence is a **re-ranking**: `callable_deps` is no longer the
dominant HIR term, and `field_dep` and `declared_dep` have taken its place —
`declared_dep` purely by standing still while everything around it fell.

What remains in these terms is flat per-call work spread over a large call
count, not a second superlinear defect. The single exception, and the subject of
the rest of this record, is the MISS fallback — which is charged to `sigtype`,
`project` and `field_dep`, and is therefore part of the residual that the
measurement above leaves in those three.

## Root cause

When `lookup_qualified_type_raw` misses, `imported_surface_type_projected`
falls back to `lower_named_kind`, whose default arm calls
`try_register_glob_reachable_symbol`
(`20.hir/hir_lowering/_Items/module_import_registration.spl`).

That sweep has **no early exit on failure** — to prove no route exists it must
visit every glob target of the importer — and **nothing remembered the
failure**. Per call it:

1. rebuilt the importer key from `self.module_filename` by three string
   rewrites (`ends_with`/slice, `replace("/", ".")`, `substring`) and
   re-resolved it through `surface_index_for_name`;
2. swept every glob import row of the importer;
3. asked `hir_module_declares_item(target, name)` for each — **six linear
   `module_surface_name_position` scans** over the target surface's name
   arrays. This is the identical question NAMEIDX (2026-08-22) had already
   converted to a Dict probe inside `register_imported_symbol_inner`; this call
   site was never converted.

run12's own counters size the call volume: **1,251,806 of 1,496,719** qualified
-type probes (84%) took the miss path that lands here. So the unmemoized sweep
ran on the order of 1.25M times per stage-1 build at O(glob targets x 6 linear
surface name scans) each — charged to whichever profile slot the caller was in,
i.e. `sigtype`, `project` and `field_dep`, the very terms left standing.

Same defect family as the rest of this subsystem's 2026-08-21/22 work (PKGDEP,
PKGIDX, IMPLIDX, NAMEIDX, REXMEMO, RISDONE, QTYPEIDX): an answer that is a pure
function of the frozen registry, recomputed per occurrence.

## Fix

GLBMEMO, in `try_register_glob_reachable_symbol`:

- **Negative memo** `glob_reachable_miss_memo`, keyed
  `{generation} {importer surface index} {name}`. Only failures are recorded —
  a success returns before the write.
- **Cached importer index** (`glob_reachable_importer_index` /
  `glob_reachable_importer_owner`), so a repeat name in one module does not
  rebuild the key by three string rewrites and re-resolve it.
- `hir_module_declares_item` routed through the existing NAMEIDX per-surface
  index via a new `surface_declares_item_indexed`. Same predicate: the index is
  built by one sweep per surface over the same six arrays, first occurrence
  wins, keyed on the frozen registry so it is shared across importers.
- `glob_reachable_scan_count`, an observable mechanism counter, same role as
  `explicit_dep_scan_count`.

### Why the negative memo is safe

A recorded failure can never have become a success:

- The two questions the sweep asks — `hir_module_declares_item` and
  `find_reexport_source` — are pure functions of the frozen registry, and the
  key carries `generation`, so a re-frozen registry cannot be answered from a
  stale entry.
- The one importer-local step, `register_imported_symbol`, writes into the
  importing module's symbol table — which is exactly why the key carries the
  **importer surface index** and the memo is *not* shared across importers the
  way the registry-pure `explicit_dep_target_memo` is. Within one importer a
  repeat of that registration is already suppressed by the RISDONE memo, so a
  second sweep is guaranteed to reach the same `false`.
- A name that becomes bound by some other route in the meantime never reaches
  the memo at all: the `lookup_or_invalid` guard at the top of the function
  returns first.

## Reproduce / regression pin

`test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl` — 5 rows,
following the counter-based pattern of the existing
`hir_import_registration_cost_spec.spl`. The observable is the sweep COUNT, not
a wall clock, so the spec discriminates the algorithm rather than the machine
and a faster box cannot satisfy it:

- the same unbound name asked three times sweeps **once**;
- a different name still sweeps (the memo is per name, not a latch);
- a different importer still sweeps (the memo is not shared across modules);
- `surface_declares_item_indexed` agrees with `hir_module_declares_item`;
- correctness: a memoized miss still defines no symbol.

Pre-fix the counter does not exist, so the spec cannot compile, let alone pass —
the same "cannot pass on the pre-fix code" argument
`hir_import_registration_cost_spec.spl` states in its own header. The isolating
control is stronger and was run: with **only** the memo lookup disabled
(`if false and ...`) and everything else including the counter left in place,
row 1 fails at 3 sweeps instead of 1. That pins the memo, not the counter, as
the variable.

Perf gate rows: `scripts/check/check-perf-regression-tests.shs` (`GLBMEMO`).

## Related

- `hir_qualified_type_lookup_linear_scan_2026-08-22.md` (QTYPEIDX) — the fix
  this lane follows up, and the source of the run12 probe/miss counters.
- `hir_phase_per_module_cost_2026-08-21.md` — RISDONE / explicit-dep memo, the
  same "negative result was never remembered" shape.
- `value_semantics_cow_alias_perf_class_2026-08-21.md` — the wider defect class.
