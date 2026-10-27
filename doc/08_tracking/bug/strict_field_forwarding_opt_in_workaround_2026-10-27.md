# SIMPLE_STRICT_FIELD_FORWARDING opt-in is a workaround

Bug id: `strict-field-forwarding-opt-in-20261027`. Date: 2026-10-27. Status: open.
Req: REQ-SELFHOST-ACCESSOR-001/002. Owner: compiler 20.hir lane.

## Workaround
`src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl` keeps the
undefined-field hard error behind `SIMPLE_STRICT_FIELD_FORWARDING=1`
(`# @workaround bug=strict-field-forwarding-opt-in-20261027 ...` on the state var),
because `src/compiler` itself may read fields that exist nowhere. Default (flag off)
now emits a compiler WARNING, never an error:

    [W-HIR-FIELD-001] undefined field `x` at <file>:<line>; no get_/is_ accessor forwards it[; did you mean field `f` / method `get_f`?]

Deduped by file+line+name. Emitted through `HirLowering.warning` (recovered
diagnostic channel, same as `[W-ANY-COMPILE-001]`).

## Removal plan
1. Run the sweep below with the full module graph and fix every flagged read in `src/compiler`.
2. Make the strict check unconditional (warning becomes the error) and delete
   `strict_field_forwarding_enabled`, `_state`, `_reset`, the env read and the spec's flag cases.
3. Delete this doc and the `@workaround` tag.

## Census (2026-10-27)
Method: one `simple run` process looping `parse_full_frontend` + `HirLowering.with_filename`
+ `lower_module` over each file, counting `W-HIR-FIELD-001` messages (~4 s per 30 files).
Sweep: 10.frontend 204 files, 20.hir 104, 50.mir 165, 80.driver first 200 of 454 = 673 files.
Result: 0 warnings in 0/673 files. Top offending names: none.
Caveat: **LOWER BOUND**, not a measurement of the whole compiler. Per-file lowering has no imported type tables, so reads on
imported owners have owner_id < 0 and are never checked; only same-file types are covered
(harness validated on a fixture: 2/2 warnings). A true count needs lowering with the full
module graph (driver path); not done in the light lane. Extrapolation from same-file
coverage: 0 / ~1570 compiler files, unproven for cross-file owners.

Next step: rerun the census with the full module graph (imported type tables) once the
phase-3 full CLI exists; use that count to size step 1 of the removal plan.

- **DB reconciliation pending:** bug id `strict-field-forwarding-opt-in-20261027` is not in bug_db.sdn yet; add it with `bin/simple bug-add` when the DB lane allows it.
