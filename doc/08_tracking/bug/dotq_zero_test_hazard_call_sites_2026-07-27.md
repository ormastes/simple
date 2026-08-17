# Containment: `.?` zero-test hazard call sites (lane NILQ)

- **Filed:** 2026-07-27
- **Lane:** NILQ
- **Companion:** `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md`
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Method

`.?` occurrences in owned `src/**` (excluding `src/compiler/**`,
`src/compiler_rust/**`, `src/lib/common/convert.spl`, `src/lib/common/ui/**`,
`src/os/services/llm/**`, `src/lib/*/ecs/**`, `src/os/kernel/**`,
`src/lib/gc_async_mut/gpu/browser_engine/**`):

| set | count |
|---|---|
| lines containing `.?` | 1,216 |
| in a guard position (`if` / `while` / `not` / `expect`) | 347 |
| of those, **bare truthiness** (no `if val` binding) | 347 |
| **hazardous** — receiver can legitimately be 0 | **23** |
| benign — `Option<struct/handle>` receivers | ~324 |

The benign majority are `*_opt` receivers holding an `Option` of a struct or
handle. For those the JIT's mis-lowering is harmless: `None` is 0 → false and
`Some(ptr)` is a non-null pointer → true, which coincides with the specified
presence semantics. Only receivers whose *payload* can be 0 (or which are a
plain integer) are affected.

## Hazardous sites repaired (23)

### Class A — plain `i64` search results with a `-1` not-found sentinel (14)

`index_of` / `last_index_of` / `find` return a **plain i64, -1 for not found**
(verified on both engines: `build/nilq_probe/idx2.spl`). Guarding them with
`.?` is wrong in **both** directions: on the JIT it fires for a real match at
index 0, and it never fires for the -1 sentinel (-1 is non-zero → truthy).
Migrated to an explicit `< 0` sign test.

- `src/lib/nogc_sync_mut/ftp_utils.spl` — L169, L172, L223, L235, L455, L458
  (`start_idx`, `end_idx`, `last_slash`)
- `src/lib/nogc_async_mut/ftp_utils.spl` — L169, L172, L225, L237, L457, L460
- `src/lib/nogc_sync_mut/env/variables.spl` — L360 (`dollar_pos` from `find("$")`)
- `src/lib/nogc_async_mut/env/variables.spl` — L356 (same)

The sync `variables.spl` already carried the correct idiom eleven lines lower
(`if close_offset >= 0:` with the comment "find returns a plain i64 (-1 == not
found), not an Option") — the `.?` guard above it was simply inconsistent with
its own file. The async copy additionally destructured the plain i64 with
`match dollar_pos: Some(offset) / nil`, which is the "`Some(_)` silently
accepted on a non-Option" trap; that was removed in the same edit.

### Class B — genuine `Option<i64>` whose payload can be 0 (9)

Migrated to `== nil` / `!= nil`, verified 15/15 correct and mutually consistent
on both engines (`build/nilq_probe/tt_cmp.spl`).

- `src/lib/nogc_sync_mut/database/test_extended/queries.spl` — L43, L84
- `src/lib/nogc_sync_mut/database/test_extended/database.spl` — L629, L667
  (`file_id_opt`, `suite_id_opt`: a row with id 0 was invisible)
- `src/lib/nogc_async_mut/async_host/scheduler.spl` — L228, L234 (`task_id`),
  L238 (`stolen`, the positive form → `!= nil`)
- `src/lib/nogc_async_mut/async_host/worker_thread.spl` — L80 (`task_id`)
- `src/app/interpreter/async_runtime/actor_scheduler.spl` — L550 (`actor_id`)

Task and actor ids are 0-based, so `Some(0)` is a live value: on the JIT the
scheduler treated a validly-popped task 0 as "no work", falling through to the
global queue and then to work-stealing — a duplicate-dispatch hazard.

## Verification performed

- **Lint:** every edited file re-linted and A/B'd against its `HEAD` version.
  Error counts are identical to baseline (`variables.spl` 2 = 2,
  `ftp_utils.spl` 13 = 13) — **zero new lint errors introduced**.
- **New spec:** `test/01_unit/language/nil_presence_idioms_spec.spl`, lint-clean
  but **never executed** — see below.

### `simple test` exits 0 without running any example (separate defect)

`bin/simple test build/nilq_probe/vacuous_spec.spl` **exited 0** after emitting
901 bytes consisting solely of lint warnings, with **zero**
`"N examples, M failures"` lines. Since sspec prints one such line per
`describe` block, their total absence means no example was scheduled. Exit 0
with nothing run is a **false green** that any CI would score as PASS.

This is why no PASS is claimed for the new spec here, and why every assertion in
it was instead verified individually through `bin/simple run` on both engines
before being written down. It also means green `simple test` results in this
worktree are not, on their own, evidence that anything was checked — worth a
dedicated lane.

### Honest limitation on the end-to-end A/B

An end-to-end A/B of `expand_var` (working tree vs `HEAD`) produced **identical
correct output for both versions**, i.e. it did *not* reproduce the failure.
Reason: that module fails JIT compilation in this harness
(`higher_layer_runtime_family` restriction) and **falls back to the
interpreter**, where `.?` is correct — so the buggy path is not reachable there.
The hazard is demonstrated generically instead, by the isolated truth table
(`build/nilq_probe/tt_dotq.spl`), which shows `Some(0).?` → `false` and
`(0).?` → `false` on the JIT.

The repairs are therefore justified as **engine-independence** fixes: after
them, these guards behave identically under both engines and no longer depend
on which one happens to run the module. No claim is made that a user-visible
runtime failure was reproduced in `expand_var`.

## NOT repaired — 1,954 vacuous `expect(X.?)` assertions

`grep -rnE 'expect\([A-Za-z_][A-Za-z0-9_.]*\.\?\)' src/ test/` (exclusions
applied) finds **1,954** sites, e.g.
`src/lib/nogc_sync_mut/debug/formats/test/golden_elf_dwarf_spec.spl` L274-299.

None of them is a presence assertion:

- on the **interpreter** `.?` returns `T?`, so `expect(x.?).to_equal(true)`
  compares an optional against a bool and asserts nothing;
- on the **JIT** `.?` returns a bool, so it does assert — but it asserts
  truthiness, i.e. `x != 0` for integers and a **constant `true`** for every
  `text` or array receiver.

These were deliberately **not** bulk-rewritten: converting them makes ~2k
currently-green assertions start actually asserting, which must be triaged as
its own campaign rather than smuggled into a containment lane. Rewrite them to
`!= nil` / `== nil` (or `.len() > 0` where emptiness is the real intent) only
behind a dedicated lane with per-file red/green review.
