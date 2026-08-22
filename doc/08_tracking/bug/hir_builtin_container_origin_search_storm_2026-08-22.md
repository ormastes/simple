# HIR payload/callable origin search storm on builtin container spellings

- **Date:** 2026-08-22
- **Area:** `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
- **Class:** cost, not correctness (no terminal error was produced by the defect)
- **Related:** `hir_unresolved_type_owner_missing_import_2026-08-22.md` (the advisory
  this record is about), `hir_phase_per_module_cost_2026-08-21.md` (the "87
  payload-origin searches for builtin names" item),
  `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md` iteration 4
  (the 97.1% `visited-memo` chase-bail census)

## Symptom

Stage-1 `run14` (log `$S/stage1_build14.log`) emitted roughly **31,700 in-flight
advisory lines for BUILTIN CONTAINER type names alone**:

| name | advisory lines |
|---|---|
| `Dict` | 14,847 |
| `Option` | 9,857 |
| `Result` | 7,015 |
| `fn` | 290 |

None of them is a terminal error. Every one is emitted after a **full failed
origin search**: `resolve_materialized_enum_payload_origin` asks the declaring
module for a declaration, then walks its re-export routes, then sweeps its whole
explicit import table — and then the callable twin sweeps the import table
again. That work is repeated per occurrence of the name and per importing
module, and its answer depends only on the frozen module-surface registry.

## Why the obvious fix is WRONG

Commit `1aa81cac8c6` added `hir_dependency_is_builtin_type` and deliberately
made it **lowercase-primitives-only, plus `Any`**. `lower_named_kind` places the
builtin container arms **after** the symbol lookup precisely so that a user type
of the same name wins, and such declarations really exist in this tree: 42
`Result`, 14 `Option`, 10 `Array`, 7 `List`, 4 `Set`, 4 `Map`, 1 `Dict`, plus
`struct Bool`. Extending the filter to capitalized/container spellings would
silently stop materializing real user types — a correctness regression sold as
noise reduction.

## Fix: a NEGATIVE memo keyed on (owner, name)

`payload_origin_miss_memo: {text: bool}` on `HirLowering`, keyed
`hir_payload_origin_miss_key(owner_key, name)` = `"{owner key} {name}"`.

- **Only a MISS is cached.** A hit is never recorded, so a module that really
  declares `Result`/`Dict`/`Option` resolves on step 1 of every search and the
  declared-type-wins precedence is untouched. This is what makes the fix sound
  where a name filter is not: the memo can only ever short-circuit a search
  whose answer was *already* "this owner does not have it".
- **Sound to cache at all** because `resolve_materialized_enum_payload_origin`
  is a pure function of (owner surface, name) over the frozen `module_surfaces`
  set: it reads no symbol table and mutates nothing. Same invariance argument
  `explicit_dep_target_memo` already rests on.
- **Owner-scoped, never global by name.** Two modules may spell the same name
  and only one declare it, so a name-keyed memo would be unsound.
- The advisory is emitted **once per (owner, name)** instead of once per
  occurrence, for the same reason: repeats carry no new information.
- The callable path's advisory dedupe uses a **separate key namespace**
  (`"callable " + owner`). Its negative ("no explicit import declares it") is
  *narrower* than the payload search's negative, so letting one suppress the
  other would skip a resolution that could still succeed.

`payload_origin_miss_skip_count` counts memo hits — the observable the spec
pins.

## Reproduce / regression spec

`test/01_unit/compiler/hir/hir_payload_origin_miss_memo_spec.spl` (5 examples).
Pins a COUNT, not a wall clock, so it discriminates the algorithm rather than
the machine and cannot pass on the pre-fix code (the counter did not exist).

- three importers × one owner × `Dict` ⇒ exactly 1 search, 2 memo hits
- `Option`/`Result`/different-owner keys stay distinct (3 entries, 0 hits)
- **CONTROL:** an owner that DECLARES `enum Result` still resolves to its own
  declaration (`found`, `item_kind == "enum"`) and is **never** entered in the
  miss memo
- `hir_dependency_is_builtin_type` still filters only lowercase primitives —
  `Dict`/`Option`/`Result` stay unfiltered
- a memoized miss raises no diagnostic and defines no symbol, for every importer

Measured: 5/5 PASS post-fix; pre-fix the spec does not compile (the memo field
and counter do not exist).

## Gate

`scripts/check/check-perf-regression-tests.shs` rows `PAYLOADMISS *` (6 rows):
the memo probe precedes the search, the key is owner-scoped, the callable
keyspace stays separate, the builtin filter stays lowercase-only, and both spec
observables are pinned. Measured `PASS — 108 mechanism(s) checked, 0 regressed`.

## Measured before/after

Same deployed seed (`/mnt/data/worktrees/goal-main-1/bin/simple`), same command
(`run src/app/cli/bootstrap_main.spl compile --format=smf <module>`), BEFORE run
in a pristine `origin/main` worktree and AFTER in the fix worktree, launched
concurrently so both see the same box load (a shared host also running stage-1
`run14` — treat the wall numbers as an envelope, the COUNTS as the real signal).

| module | advisories before | after | wall before | wall after |
|---|---|---|---|---|
| `src/compiler/50.mir/mir_lowering_types.spl` | 1,484 | **40** (-97.3%) | 207.4 s | **160.4 s** (-22.6%) |
| `.../20.hir/hir_lowering/_Items/module_reexport_materialization.spl` | 4,608 | **70** (-98.5%) | 914.9 s | 932.0 s (+1.9%) |

Per-name, module 1 before: `Dict` 750, `Option` 565+77, `Result` 31, `fn` 9 —
after, each collapses to one line per (owner, name) (`Option` 16 distinct
owners, `Dict` 6, `Result` 4). That is the O(1)-per-name shape the spec pins.

**Stated rather than papered over:** the wall gain is real on module 1 and is
*noise* on module 2 (+1.9%). The counts are unambiguous on both; the wall was
measured on a contested box under a concurrent multi-hour stage-1 run, so a
single-digit-percent wall delta there does not discriminate. The claim this
record supports is the search/advisory count, not a wall-clock budget.
